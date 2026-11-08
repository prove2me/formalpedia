-- Prove2me | Definitions.Def_BipColorHard_Objective
-- name    : BipColorHard_Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:35.775414+00:00
-- url     : https://prove2.me/theorems/e505aba4-9e02-4957-9868-791cbe83734b
-- title:
--   The objective $L$, $\Phi$; stationary pairs, types, phases, $T_0$ and negative definiteness
-- statement:
--   Let $B=J-I_q$. For nonzero nonnegative vectors $x,y\in\mathbb R^q$ and $\|x\|_p=(\sum_i|x_i|^p)^{1/p}$,
--   $$L(x,y)=\frac{x^{\mathsf T}By}{\|x\|_p\|y\|_p},\qquad \Phi(P,R)=(d+1)\log L(P,R),\quad p=\frac{d+1}{d}.$$
--   A **stationary pair** of $\Phi$ has all coordinates positive and all first partial derivatives zero. The **types** of a pair are the classes of colors on which both vectors agree. A **phase** is a maximizer of $L$ over nonzero nonnegative vectors, each normalized to coordinate sum one. The tangent space of both normalizations is
--   $$T_0=\Big\{(u,v)\in\mathbb R^q\times\mathbb R^q:\sum_i u_i=\sum_i v_i=0\Big\}.$$
--   The Hessian of $f$ at $(P,R)$ is **negative definite on $T_0$** when $f$ restricted to $(P,R)+T_0$ is twice continuously differentiable at $(P,R)$ and its second derivative in every nonzero direction of $T_0$ is negative.
--
--   For a partition $[q]=I\cup I^{\mathrm c}$ into nonempty sets, the two-type problem maximizes $\Phi$ over sum-normalized pairs constant on $I$ and on $I^{\mathrm c}$; its value is $V$.
--
--   These functions are the optimization problem that determines the phases of the random bipartite base graph.
--
--   **Formalization Note** $\Phi$ is defined in the manuscript when $P^{\mathsf T}BR>0$. Stationarity, local maxima and phases are evaluated at positive pairs, where the logarithm is finite, and the two-type problem requires $P^{\mathsf T}BR>0$. $V$ is a real supremum over a nonempty bounded set, indexed by the set $I$.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §7.1, pp.30–31 (PDF pp.32–33); §7.2, p.33 (PDF p.35); §7.3, p.34 (PDF p.36); Lemma 12, pp.12–13 (PDF pp.14–15)

import Mathlib

set_option autoImplicit false

namespace BipColorHard

variable {q : ℕ}

/-- `xᵀBy` with `B = J - I_q`: the sum of `x_i y_j` over `i ≠ j`. Galanis, Guo, He, Štefankovič, Vigoda,
manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §7.1, p.30 (PDF p.32). -/
def bipForm (x y : Fin q → ℝ) : ℝ := ∑ i, ∑ j, if i = j then 0 else x i * y j

/-- `‖x‖_p = (∑ |x_i|^p)^{1/p}`, §7.1, p.30 (PDF p.32). -/
noncomputable def pNorm (p : ℝ) (x : Fin q → ℝ) : ℝ := (∑ i, |x i| ^ p) ^ (1 / p)

/-- `L(x, y) = xᵀBy / (‖x‖_p ‖y‖_p)`, §7.1, p.30 (PDF p.32).

**Formalization Note.** Meaningful for nonzero nonnegative vectors, as in the manuscript. Lemma 12 prints
the numerator as `1 - ∑ P_i R_i`, which agrees with `PᵀBR` on probability vectors. -/
noncomputable def objL (p : ℝ) (x y : Fin q → ℝ) : ℝ := bipForm x y / (pNorm p x * pNorm p y)

/-- `Φ(P, R) = (d + 1) log L(P, R)` with `p = (d + 1)/d`, (30), p.30 (PDF p.32).

**Formalization Note.** The manuscript defines `Φ` when `PᵀBR > 0`. Every use below is at positive vectors,
or restricted to `PᵀBR > 0`, so the logarithm's argument is positive. -/
noncomputable def objPhi (d : ℕ) (P R : Fin q → ℝ) : ℝ :=
  ((d : ℝ) + 1) * Real.log (objL (((d : ℝ) + 1) / d) P R)

/-- A **stationary pair** of `Φ`, §7.1, p.31 (PDF p.33): all coordinates strictly positive, and all first
partial derivatives with respect to the coordinates of `P` and `R` vanish. -/
def IsStationary (d : ℕ) (P R : Fin q → ℝ) : Prop :=
  (∀ i, 0 < P i) ∧ (∀ i, 0 < R i) ∧
    (∀ i, HasDerivAt (fun t => objPhi d (Function.update P i t) R) 0 (P i)) ∧
    ∀ i, HasDerivAt (fun t => objPhi d P (Function.update R i t)) 0 (R i)

/-- The number of **types** of a pair: the classes of colors on which both vectors agree, §7.2,
p.33 (PDF p.35). -/
noncomputable def typeCount (P R : Fin q → ℝ) : ℕ := (Finset.univ.image fun i => (P i, R i)).card

/-- `(P, R)` is a local maximum of `Φ`, in the neighbourhoods of `ℝ^q × ℝ^q`.

**Formalization Note.** Used at positive pairs, which have a positive neighbourhood; `Φ` is unchanged when
either vector is multiplied by a positive constant, so this agrees with local maximality under the
normalizations the manuscript uses. -/
def IsLocalMaxPhi (d : ℕ) (P R : Fin q → ℝ) : Prop :=
  IsLocalMax (fun z : (Fin q → ℝ) × (Fin q → ℝ) => objPhi d z.1 z.2) (P, R)

/-- A **phase**, §7.1, p.31 (PDF p.33), Lemma 12, p.12 (PDF p.14): a maximizing pair of `L` over nonzero
nonnegative vectors, with each vector normalized to have coordinate sum one. -/
def IsPhase (p : ℝ) (P R : Fin q → ℝ) : Prop :=
  (∀ i, 0 ≤ P i) ∧ (∀ i, 0 ≤ R i) ∧ ∑ i, P i = 1 ∧ ∑ i, R i = 1 ∧
    ∀ x y : Fin q → ℝ, (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ y i) → x ≠ 0 → y ≠ 0 →
      objL p x y ≤ objL p P R

variable (q) in
/-- `T₀ = {(u, v) : ∑ u_i = ∑ v_i = 0}`, the perturbations preserving both coordinate sums, §7.1, p.31 (PDF p.33). -/
def T0 : Submodule ℝ ((Fin q → ℝ) × (Fin q → ℝ)) where
  carrier := {w | ∑ i, w.1 i = 0 ∧ ∑ i, w.2 i = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    simp [Finset.sum_add_distrib, ha1, ha2, hb1, hb2]
  zero_mem' := by simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    simp [← Finset.mul_sum, ha1, ha2]

/-- **The Hessian of `f` at `(P, R)` is negative definite on `T₀`** (Lemma 12, p.13 (PDF p.15); Lemma 28, p.31
(PDF p.33); Lemma 34, p.42 (PDF p.44); Lemma 35, p.46 (PDF p.48)): the restriction
`w ↦ f (P + w₁) (R + w₂)` of `f` to the affine space through `(P, R)` with direction `T₀` is twice continuously
differentiable at `w = 0`, and its second derivative at `0` is negative at `(w, w)` for every `w ≠ 0`.

**Formalization Note.** The restriction to `T₀` is what makes this meaningful for `Ψ`, which is only defined
on pairs of probability vectors. -/
def HessNegDefOnT0 (f : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (P R : Fin q → ℝ) : Prop :=
  ContDiffAt ℝ 2 (fun w : T0 q => f (P + w.1.1) (R + w.1.2)) 0 ∧
    ∀ w : T0 q, w ≠ 0 →
      iteratedFDeriv ℝ 2 (fun w : T0 q => f (P + w.1.1) (R + w.1.2)) 0 ![w, w] < 0

/-- `x` is constant on the set of colors `I`. -/
def ConstOn (I : Finset (Fin q)) (x : Fin q → ℝ) : Prop := ∀ i ∈ I, ∀ j ∈ I, x i = x j

/-- The pair `(P, R)` is admissible for the two-type problem of §7.3, p.34 (PDF p.36) on the partition
`[q] = I ∪ Iᶜ`: both vectors have coordinate sum one and are constant on `I` and on `Iᶜ`.

**Formalization Note.** `Φ` is defined when `PᵀBR > 0`, §7.1; a pair with `PᵀBR = 0` has value `-∞` and is
not admissible here. -/
def TwoTypeFeasible (I : Finset (Fin q)) (P R : Fin q → ℝ) : Prop :=
  (∀ i, 0 ≤ P i) ∧ (∀ i, 0 ≤ R i) ∧ ∑ i, P i = 1 ∧ ∑ i, R i = 1 ∧
    ConstOn I P ∧ ConstOn Iᶜ P ∧ ConstOn I R ∧ ConstOn Iᶜ R ∧ 0 < bipForm P R

/-- A maximizing pair of the two-type problem, §7.3, p.34 (PDF p.36). -/
def IsTwoTypeMax (d : ℕ) (I : Finset (Fin q)) (P R : Fin q → ℝ) : Prop :=
  TwoTypeFeasible I P R ∧ ∀ P' R', TwoTypeFeasible I P' R' → objPhi d P' R' ≤ objPhi d P R

/-- `V`, the maximum of `Φ` over pairs admissible for the partition `[q] = I ∪ Iᶜ`, §7.3, p.34 (PDF p.36).

**Formalization Note.** The manuscript writes `V(s)` with `s = |I|`, having observed that the value depends only
on `s`; here it is indexed by `I`. The set is nonempty (uniform vectors) and bounded above (`L` is bounded on
sum-normalized vectors), so the real `sSup` is the maximum. -/
noncomputable def twoTypeV (d : ℕ) (I : Finset (Fin q)) : ℝ :=
  sSup {v | ∃ P R, TwoTypeFeasible I P R ∧ v = objPhi d P R}

end BipColorHard


