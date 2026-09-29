-- Prove2me | Definitions.Def_WangZahlKakeya_wolff
-- name    : WangZahlKakeya_wolff
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T11:10:43.246041+00:00
-- url     : https://prove2.me/theorems/4f94957a-7403-4772-8375-6f4981ab635a
-- title:
--   Shaded tube systems and the Katz--Tao Convex / Frostman Slab Wolff constants
-- statement:
--   This file encodes the standing set-up of Wang–Zahl §1.2 and §3.1: a finite family of essentially distinct $\delta$-tubes in the unit ball together with a shading, and the two non-clustering constants of Definition 1.3.
--
--   A **system of $\delta$-tubes with shading**, written $(\mathbb{T},Y)_\delta$, consists of $n$ base points $p_i$ and directions $v_i$ together with sets $Y_i$, subject to: $\delta > 0$; every $v_i$ is a unit vector; every tube $T_i = T(p_i,v_i,\delta)$ lies in the closed unit ball; the tubes are pairwise **essentially distinct**, i.e.
--
--   $$|T_i \cap T_j| \le \tfrac12 \max\big(|T_i|, |T_j|\big) \qquad (i \ne j);$$
--
--   and each $Y_i$ is a measurable subset of $T_i$. The **shaded union** is $\bigcup_i Y_i$, and the system is **$\lambda$-dense** when
--
--   $$\sum_{i} |Y_i| \;\ge\; \lambda \sum_i |T_i| \;=\; \lambda\, n\, |T| ,$$
--
--   where $|T|$ denotes the common volume of a $\delta$-tube.
--
--   For a set $W$, $\#\mathbb{T}[W]$ denotes the number of tubes of the family contained in $W$. The two Wolff constants of Definition 1.3 are then
--
--   $$C_{\mathrm{KT\text{-}CW}}(\mathbb{T}) = \inf\Big\{C>0 : \#\mathbb{T}[W] \le C |W| |T|^{-1} \text{ for every convex } W \subseteq \mathbb{R}^3 \Big\},$$
--
--   $$C_{\mathrm{F\text{-}SW}}(\mathbb{T}) = \inf\Big\{C>0 : \#\mathbb{T}[W] \le C |W| (\#\mathbb{T}) \text{ for every slab } W \subseteq \mathbb{R}^3\Big\}.$$
--
--   The first measures *sparsity* — how few tubes can be packed into a convex set relative to its volume — and the second measures *non-concentration in planes*. A family of $\delta$-tubes coming from a Kakeya set, one tube in each $\delta$-separated direction, obeys both with error $O(1)$.
--
--   These quantities are the hypotheses and the parameters of Assertions $D$ and $E$, which are the objects the paper inducts on.
--
--   **Formalization Note** A family of tubes is indexed by $\{0,\dots,n-1\}$ rather than given as an abstract finite set; essential distinctness is imposed as a hypothesis on the indexed family, so distinct indices may not be assumed to give distinct tubes beyond what that hypothesis gives. The defining inequality of each constant is stated in the extended nonnegative reals and in product form (no division), so convex sets of infinite volume are handled correctly; the constant itself is the infimum of a set of positive reals, and equals $0$ when that set is empty.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, §1.2 (Definition 1.3, Remark 1.4), §3.1 (Definitions 3.1--3.2) and §4.1 (Definition 1.3', Remark 4.2)

import Definitions.Def_WangZahlKakeya_geometry

/-!
# Tube systems, shadings and Wolff axioms

Formalizes the standing set-up of Wang–Zahl, *Volume estimates for unions of convex sets,
and the Kakeya set conjecture in three dimensions* (arXiv:2502.17655v1), §1.2 and §3.1:
a finite family `(T, Y)_δ` of essentially distinct `δ`-tubes contained in the unit ball,
together with a shading, its density, and the Katz–Tao Convex Wolff and Frostman Slab Wolff
constants of Definition 1.3.
-/

namespace WangZahlKakeya

open MeasureTheory Metric Set
open scoped ENNReal

/-- The family `(T, Y)_δ` is a legitimate system of `δ`-tubes with a shading:
`δ > 0`; the directions `v i` are unit vectors; every tube is contained in the closed unit
ball; the tubes are pairwise essentially distinct, i.e. any two of them meet in a set of
volume at most half the larger of their volumes; and each `Y i` is a measurable subset of
the `i`-th tube. -/
def IsTubeSystem (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3) : Prop :=
  0 < δ ∧
  (∀ i, ‖v i‖ = 1) ∧
  (∀ i, tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1) ∧
  (∀ i j, i ≠ j →
    volume (tube (p i) (v i) δ ∩ tube (p j) (v j) δ) ≤
      (volume (tube (p i) (v i) δ) ⊔ volume (tube (p j) (v j) δ)) / 2) ∧
  (∀ i, Y i ⊆ tube (p i) (v i) δ) ∧
  (∀ i, MeasurableSet (Y i))

/-- The union `⋃_{T ∈ T} Y(T)` of the shaded parts of the tubes. -/
def shadingUnion {n : ℕ} (Y : Fin n → Set E3) : Set E3 := ⋃ i, Y i

/-- The number of tubes of the family that are contained in the set `W`, i.e. `#T[W]`. -/
noncomputable def tubeCountIn (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (W : Set E3) : ℕ :=
  {i : Fin n | tube (p i) (v i) δ ⊆ W}.ncard

/-- `(T, Y)_δ` is `λ`-dense: `∑_T |Y(T)| ≥ λ ∑_T |T|`. -/
def IsDenseSystem (δ : ℝ) (n : ℕ) (Y : Fin n → Set E3) (lam : ℝ) : Prop :=
  ∑ i, (volume (Y i)).toReal ≥ lam * ((n : ℝ) * tubeVol δ)

/-- The Katz–Tao Convex Wolff constant `C_{KT-CW}(T)` (Definition 1.3(A)): the infimum of
all `C > 0` such that `#{T ∈ T : T ⊆ W} ≤ C |W| |T|⁻¹` for every convex set `W ⊆ ℝ³`.
The inequality is written in the equivalent product form `#T[W] · |T| ≤ C · |W|` inside the
extended nonnegative reals, so that convex sets of infinite volume cause no difficulty. -/
noncomputable def KTCW (δ : ℝ) (n : ℕ) (p v : Fin n → E3) : ℝ :=
  sInf {C : ℝ | 0 < C ∧ ∀ W : Set E3, Convex ℝ W →
    (tubeCountIn δ n p v W : ℝ≥0∞) * ENNReal.ofReal (tubeVol δ) ≤
      ENNReal.ofReal C * volume W}

/-- The Frostman Slab Wolff constant `C_{F-SW}(T)` (Definition 1.3(B)): the infimum of all
`C > 0` such that `#{T ∈ T : T ⊆ W} ≤ C |W| (#T)` for every slab `W ⊆ ℝ³`. -/
noncomputable def FSW (δ : ℝ) (n : ℕ) (p v : Fin n → E3) : ℝ :=
  sInf {C : ℝ | 0 < C ∧ ∀ W : Set E3, IsSlab W →
    (tubeCountIn δ n p v W : ℝ≥0∞) ≤ ENNReal.ofReal C * volume W * (n : ℝ≥0∞)}

end WangZahlKakeya


