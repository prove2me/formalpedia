-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Supplement_Purification
-- name    : RandomDimReduction_Channel_Supplement_Purification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:42.34791+00:00
-- url     : https://prove2.me/theorems/e793b206-703d-4baa-9862-7e03c3b6eb1e
-- title:
--   Entangled vectors and the three explicit random purification maps
-- statement:
--   For a finite orthonormal basis $A$, let $|\Gamma_A\rangle=\sum_i|i,i\rangle$, without normalization. A purification $\phi$ of $\rho$ is a unit vector on $A\otimes B$ whose partial trace over $B$ is $\rho$. The canonical regrouping sends $((a_t,b_t))_{t=1}^n$ to $((a_t)_t,(b_t)_t)$, and reindexes tensor operators accordingly.
--
--   For an operator map $N$, its reference-first Choi matrix has blocks $N(|i\rangle\langle j|)$. With the published reduction map $R$, not $R^{TP}$, put
--   $$J_R=(\mathrm{id}\otimes R)(|\Gamma\rangle\langle\Gamma|),\qquad P(X)=J_R(X\otimes I).$$
--   Let $T_{S_n}(X)=\frac1{n!}\sum_\pi F_\pi XF_\pi^\dagger$. The other two explicit maps are
--   $$P^{CP}(X)=P(T_{S_n}(X)),\qquad P^{CPTP}(X)=P^{CP}(X)+\frac{\operatorname{tr}(QX)}{k^nd^n}I,$$
--   where $Q$ is the published kernel projector. No positivity, normalization or purification guarantee is imposed by these definitions. The target average independently conjugates a fixed purification by $I\otimes V$, takes its $n$-fold tensor power and regroups the registers, then integrates over normalized Haar $V\in U(k)$.
--
--   These definitions implement Eqs. (4)–(6) literally and supply the registers for Lemma 2.1 and Theorem 3.1.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, §2.1, pp.5–6; §3.1, pp.8–10, Eqs. (4)–(6)

import Definitions.Def_RandomDimReduction_Channel_Moment

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Kronecker Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnormalized maximally entangled vector, §2.1, p.5. -/
def gamma (a : Type) [DecidableEq a] : a × a → ℂ :=
  fun ij => if ij.1 = ij.2 then 1 else 0

/-- The canonical regrouping (A ⊗ B)^n ≃ A^n ⊗ B^n. -/
def regroup {a b : Type} (n : ℕ) :
    (Fin n → a × b) ≃ ((Fin n → a) × (Fin n → b)) where
  toFun x := (fun t => (x t).1, fun t => (x t).2)
  invFun x := fun t => (x.1 t, x.2 t)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex an operator into the grouped tensor registers. -/
def groupOperator {a b : Type} (n : ℕ) (X : Op (Fin n → a × b)) :
    Op ((Fin n → a) × (Fin n → b)) :=
  fun i j => X ((regroup n).symm i) ((regroup n).symm j)

/-- Unnormalized reference-first Choi operator; §2.1, p.6. -/
def choi {a b : Type} [DecidableEq a] (N : Op a → Op b) : Op (a × b) :=
  fun i j => N (Matrix.single i.1 j.1 1) i.2 j.2

/-- Eq.(4): ordinary left multiplication, with neither transpose nor sandwich. -/
def purification (n k d : ℕ) (X : Op (Word n d)) : Op (Word n d × Word n k) :=
  choi (reduction n k d) * (X ⊗ₖ (1 : Op (Word n k)))

/-- The permutation twirl of §3.1, p.8. -/
def permutationTwirl (n d : ℕ) (X : Op (Word n d)) : Op (Word n d) :=
  ((Nat.factorial n : ℂ)⁻¹) • ∑ p : Equiv.Perm (Fin n),
    MixedCloning.Optimal.permMatrix n p * X * (MixedCloning.Optimal.permMatrix n p)ᴴ

/-- P^CP = P ∘ T_Sn, defined on the full operator algebra. -/
def purificationCP (n k d : ℕ) (X : Op (Word n d)) : Op (Word n d × Word n k) :=
  purification n k d (permutationTwirl n d X)

/-- Eq.(5), with the full output dimension k^n d^n in the denominator. -/
def purificationCPTP (n k d : ℕ) (X : Op (Word n d)) : Op (Word n d × Word n k) :=
  purificationCP n k d X +
    ((kernelProjector n k d * X).trace / ((k ^ n * d ^ n : ℕ) : ℂ)) • 1

/-- A unit vector with the specified data marginal, without selecting a purification. -/
def IsPurification {d k : ℕ} (rho : Op (Fin d))
    (phi : EuclideanSpace ℂ (Fin d × Fin k)) : Prop :=
  ‖phi‖ = 1 ∧ WildeQIT.partialTraceRight (MixedCloning.Optimal.pure phi) = rho

/-- One Haar unitary on the purifying register, shared across all n copies; Eq.(6). -/
def randomPurificationAverage {d k : ℕ} (n : ℕ)
    (phi : EuclideanSpace ℂ (Fin d × Fin k)) : Op (Word n d × Word n k) :=
  ∫ V : Matrix.unitaryGroup (Fin k) ℂ,
    groupOperator n (tensor n
      (((1 : Op (Fin d)) ⊗ₖ (V : Op (Fin k))) *
        MixedCloning.Optimal.pure phi *
        (((1 : Op (Fin d)) ⊗ₖ (V : Op (Fin k))))ᴴ))
    ∂MixedCloning.Optimal.haar k

end RandomDimReduction.Channel.Supplement


