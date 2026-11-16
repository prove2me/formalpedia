-- Prove2me | Definitions.Def_MetricSelfDualCompletion_Completion_Supplement_Recovery
-- name    : MetricSelfDualCompletion_Completion_Supplement_Recovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:15:43.820676+00:00
-- url     : https://prove2.me/theorems/9781549b-08a3-44f0-bf61-99da9e38d5d7
-- title:
--   Protected hosts, general completion and full recovery specification
-- statement:
--   Let $M\le\mathbb F_2^N$, $\tau:\mathbb F_2^m\to\mathbb F_2^N$ be linear, and $C\le\mathbb F_2^m$. Put $W=\operatorname{im}\tau$ and
--   $$K=M\cap\tau(C)^\perp,\qquad A=K+\tau(C),\qquad D=A+W.$$
--   Protection through $H$ means $\operatorname{wt}(u+\tau x)>H$ for every nonzero $u\in M$ and every $x$. The host-assumption predicate contains exactly Appendix A.1's assumptions: positive $m,s,H$, $sm\le H$, self-duality of $M$, injectivity and linearity of $\tau$, self-orthogonality of $W$, weight scaling by $s$, and protection. It contains no completion or recovery conclusions.
--
--   The recovery specification collects all algebraic clauses of Lemma 15: self-duality; the induced linear isomorphism $\mathbb F_2^m/C\simeq D/A$ and its inverse induced by recovery; all pairwise coset distances multiplied by $s$; the exact short-vector equality at every radius $0\le r\le H$ with source radius $\lfloor r/s\rfloor$; the nonzero- and zero-code distance clauses; $D=K\oplus W$ and unique decomposition; recovery $\rho(u+\tau x)=x$, $\rho\tau=\mathrm{id}$, $A=\rho^{-1}(C)$ inside $D$, and
--   $$p+\tau(\rho p)\in A,\qquad s\operatorname{wt}(\rho p)\le\operatorname{wt}(p)\quad(p\in D).$$
--   It also contains both conditional type criteria. This predicate is a theorem conclusion, not a validity promise.
--
--   A recovery output is an actual row basis of $A$ and an $m\times N$ matrix for a linear extension of $\rho$. Correctness is required only on $D$. The typed quotient is $D/(A\cap D)$, implemented by the comap along the subtype inclusion. Matrix entries are the images of standard basis vectors. The four-block map is $(x,x,x,x,0)$; the two-block map and its completion are reused from the published definitions and agree definitionally with the general formulas. Puncturing deletes the last coordinate; the Type II host interleaves two independent words of $P$ before applying the published prefix-sum construction.
--
--   These are reusable finite linear-algebra interfaces for the appendix constructions. No conclusions are supplied as axioms.
-- source:
--   Rafail Ostrovsky, STOC 2027 submission #5 (October 2026), Appendix A.1–A.3, equations (16)–(18), Lemma 15, printed p. 15–17 (PDF p. 17–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/5.pdf

import Mathlib
import Definitions.Def_MetricSelfDualCompletion_Completion_Supplement_Metrics

namespace MetricSelfDualCompletion.Completion.Supplement

open QAlgorithms

/-- Appendix A.1 equation (16), not the stronger sufficient distance assumption. -/
def Protected {m N : ℕ} (M : Code N) (τ : V m →ₗ[ZMod 2] V N) (H : ℕ) : Prop :=
  ∀ u ∈ M, u ≠ 0 → ∀ x, H < hammingNorm (u + τ x)
def generalK {m N : ℕ} (M : Code N) (τ : V m →ₗ[ZMod 2] V N) (C : Code m) : Code N :=
  M ⊓ codeDual (C.map τ)
def generalA {m N : ℕ} (M : Code N) (τ : V m →ₗ[ZMod 2] V N) (C : Code m) : Code N :=
  generalK M τ C ⊔ C.map τ
def recoveryDomain {m N : ℕ} (M : Code N) (τ : V m →ₗ[ZMod 2] V N) (C : Code m) : Code N :=
  generalA M τ C ⊔ LinearMap.range τ
/-- Restrict the target quotient to (A+W)/A. -/
def quotientKernel {m N : ℕ} (M : Code N) (τ : V m →ₗ[ZMod 2] V N) (C : Code m) :
    Submodule (ZMod 2) (recoveryDomain M τ C) :=
  (generalA M τ C).comap (recoveryDomain M τ C).subtype
/-- A matrix for a map acting on column vectors. -/
def mapMatrix {m N : ℕ} (τ : V m →ₗ[ZMod 2] V N) : Matrix (Fin N) (Fin m) (ZMod 2) :=
  fun i j => τ (Pi.single j 1) i
/-- Four whole blocks, not interleaved source coordinates. Used only with 4*m≤N. -/
def repFour (m N : ℕ) : V m →ₗ[ZMod 2] V N where
  toFun x i := if hm : 0 < m then
    if i.val < 4*m then x ⟨i.val % m, Nat.mod_lt _ hm⟩ else 0 else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
/-- The complete algebraic specification of Lemma 15. It is a conclusion, never an input oracle.
ρ is a linear extension; every nontrivial correctness condition is restricted to A+W. -/
def RecoverySpec {m N : ℕ} (s H : ℕ) (M : Code N) (τ : V m →ₗ[ZMod 2] V N)
    (C : Code m) (ρ : V N →ₗ[ZMod 2] V m) : Prop :=
  let K := generalK M τ C
  let A := generalA M τ C
  let D := recoveryDomain M τ C
  IsSelfDual A ∧
  (∃ e : (V m ⧸ C) ≃ₗ[ZMod 2] (D ⧸ quotientKernel M τ C),
    (∀ x (p : D), p.val = τ x → e (Submodule.Quotient.mk x) = Submodule.Quotient.mk p) ∧
    (∀ p : D, e.symm (Submodule.Quotient.mk p) = Submodule.Quotient.mk (ρ p))) ∧
  (∀ x y, distToCode (τ x + τ y) A = s * distToCode (x+y) C) ∧
  (∀ y (r : ℕ), r ≤ H →
    {p : V N | p + τ y ∈ A ∧ hammingNorm p ≤ r} =
      τ '' {x : V m | x+y ∈ C ∧ hammingNorm x ≤ r / s}) ∧
  (C ≠ ⊥ → minDistCode A = (s : ℕ∞) * minDistCode C) ∧
  (C = ⊥ → (H : ℕ∞) < minDistCode A) ∧
  D = K ⊔ LinearMap.range τ ∧
  Disjoint K (LinearMap.range τ) ∧
  (∀ p ∈ D, ∃! q : K × V m, p = q.1.val + τ q.2) ∧
  (∀ u : K, ∀ x, ρ (u.val + τ x) = x) ∧
  (∀ x, ρ (τ x) = x) ∧
  (∀ p ∈ D, p ∈ A ↔ ρ p ∈ C) ∧
  (∀ p ∈ D, p + τ (ρ p) ∈ A ∧ s * hammingNorm (ρ p) ≤ hammingNorm p) ∧
  (DoublyEven M → DoublyEven (LinearMap.range τ) → TypeII A) ∧
  ((∃ u ∈ M ⊓ codeDual (LinearMap.range τ), hammingNorm u % 4 = 2) → TypeI A)
/-- Just the standing assumptions of Appendix A.1. -/
def HostAssumptions {m N : ℕ} (s H : ℕ) (M : Code N) (τ : V m →ₗ[ZMod 2] V N) : Prop :=
  0 < m ∧ 0 < s ∧ 0 < H ∧ s*m ≤ H ∧ IsSelfDual M ∧ Function.Injective τ ∧
    IsSelfOrthogonal (LinearMap.range τ) ∧
    (∀ x, hammingNorm (τ x) = s * hammingNorm x) ∧ Protected M τ H
/-- Encoded output A-basis followed by an ambient recovery matrix; only its restriction matters. -/
def RecoveryOutput {m N : ℕ} (f : List Bool → List Bool) (input : List Bool)
    (s H : ℕ) (M : Code N) (τ : V m →ₗ[ZMod 2] V N) (C : Code m) : Prop :=
  ∃ (a : ℕ) (B : Matrix (Fin a) (Fin N) (ZMod 2)) (R : Matrix (Fin m) (Fin N) (ZMod 2)),
    IsRowBasis B (generalA M τ C) ∧
    f input = encMatrix B ++ encMatrix R ∧
    RecoverySpec s H M τ C (Matrix.mulVecLin R)
/-- Puncture the last coordinate, as in A.2. -/
def punctureLast (n : ℕ) (P : Code (n+1)) : Code n :=
  P.map (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin n => (i.castSucc : Fin (n+1))))
/-- A.3: interleave P⊕P; this is separate from the four-block source embedding. -/
def interleaveMap (n : ℕ) : (V n × V n) →ₗ[ZMod 2] V (2*n) where
  toFun p i := if i.val % 2 = 0 then p.1 ⟨i.val/2, by omega⟩ else p.2 ⟨i.val/2, by omega⟩
  map_add' p q := by funext i; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> rfl
  map_smul' a p := by
    funext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> rfl
def interleaveCode {n : ℕ} (P : Code n) : Code (2*n) := (P.prod P).map (interleaveMap n)

end MetricSelfDualCompletion.Completion.Supplement


