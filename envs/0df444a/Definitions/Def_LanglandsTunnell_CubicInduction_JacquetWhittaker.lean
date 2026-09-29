-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
-- name    : LanglandsTunnell_CubicInduction_JacquetWhittaker
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/9f4b030c-428b-501f-abf4-c91e35f9f8de
-- title:
--   Jacquet integrals and Whittaker functions for GL₃ cell sections
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, write $\mathbb{Q}_v$ for `v.adicCompletion ℚ` and work inside the group `LocalGL3 v` of invertible $3\times 3$ matrices over $\mathbb{Q}_v$, with $n(x,y,z)$ the upper unipotent matrix `upperUnipotent3 x y z` and $w_0$ the antidiagonal matrix `antidiagonal3 v`. For $c\in\mathbb{Z}$, `unipotentBall3 v c` is the set of triples with $v(x)\le \exp(c)$, $v(y)\le \exp(c)$ and $v(z)\le \exp(2c)$ in the value group $\mathbb{Z}_{m0}$; it increases with $c$, contains $0$, and is stable under the unipotent group law $n(x,y,z)\,n(x',y',z')=n(x+x',y+y',z+z'+xy')$ and under the corresponding inversion $(x,y,z)\mapsto(-x,-y,xy-z)$ (the radius $\exp(2c)$ in the corner coordinate is exactly what the term $xy'$ demands). The measure `jacquetHaar3 v` is the triple product of the self-dual Haar measure `selfDualHaarAt ℚ v` on $\mathbb{Q}_v$, taken for the locally installed Borel $\sigma$-algebras. The truncated Jacquet integral `jacquetTruncated3 v c u` of $u:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ is the Bochner integral over `unipotentBall3 v c` of $\psi_v(-(x+y))\,u(w_0\,n(x,y,z))$, where $\psi_v$ is `psiLocal ℚ v`; it is additive in $u$ when both integrands are integrable on the ball, and $\mathbb{C}$-homogeneous unconditionally. `jacquetLevel v u` is the infimum of the set of naturals $c_0$ with $D_c(u)=D_{c_0}(u)$ for all integers $c\ge c_0$ (hence $0$ when that set is empty), and `jacquetValue v u` is the truncated integral at that level; if some such $c_0$ exists then $D_c(u)$ equals the Jacquet value for every $c$ at least the level, and the level is bounded by any witness $c_0$. `bigCell3 v` consists of the $g$ with `cornerEntry v g` and `lowerMinor v g` non-zero, a condition unchanged by left multiplication by unipotent or diagonal matrices and containing `cellCutoff v`. For a triple $\chi$ of characters of $\mathbb{Q}_v^\times$ and $\Phi$ on $\mathbb{Q}_v^3$, `cellSectionOf v χ Φ` is the function supported on the big cell with value `cellValue v χ g * Φ (cellRatio v g)`; it is left invariant under $n(x,y,z)$, transforms by `torusChar3 v χ a * halfModulus3 v a` under left translation by `diagonal3 v a`, and reduces to `cellSection v χ` when $\Phi$ is the indicator of $\{r:\forall i,\ v(r_i)\le 1\}$ with value $1$. Finally `jacquetWhittaker3 v χ Φ` sends $g$ to the Jacquet value of the right translate $h\mapsto \mathrm{cellSectionOf}(h g)$. A further identification records that the localisation at $v$ of the standard global additive character `stdAddChar ℚ` agrees with `psiLocal ℚ v`.
--
--   **Relation to Mathlib.** Mathlib has no Jacquet integral or Whittaker functions for $\mathrm{GL}_3$; these are the project's own notions, built on Mathlib's Haar measure on the adic completion, Bochner integration and set indicators.
--
--   **Where it is used.** These are the local ingredients of the cubic induction step: the Whittaker functions of the $\mathrm{GL}_3$ principal series attached to a triple of characters, obtained as stabilised Jacquet integrals of the big-cell sections, which supply the local data for the converse theorem used in the Langlands–Tunnell input to modularity of the mod $3$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_JacquetWhittaker.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section Jacquet

variable (v : HeightOneSpectrum (𝓞 ℚ))

def unipotentBall3 (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c)}

theorem mem_unipotentBall3_iff (c : ℤ) (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    p ∈ unipotentBall3 v c ↔
      Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c) :=
  Iff.rfl

theorem unipotentBall3_mono {c c' : ℤ} (h : c ≤ c') : unipotentBall3 v c ⊆ unipotentBall3 v c' := by
  intro p hp
  simp only [mem_unipotentBall3_iff] at hp ⊢
  exact ⟨hp.1.trans (WithZero.exp_le_exp.mpr h), hp.2.1.trans (WithZero.exp_le_exp.mpr h),
    hp.2.2.trans (WithZero.exp_le_exp.mpr (by omega))⟩

theorem upperUnipotent3_mul_upperUnipotent3 {A : Type*} [CommRing A] (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem upperUnipotent3_inv_eq {A : Type*} [CommRing A] (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotent3_mul_upperUnipotent3, show x + -x = 0 by ring,
    show y + -y = 0 by ring, show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

theorem unipotentBall3_mul_mem {c : ℤ} {p p' : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (hp : p ∈ unipotentBall3 v c) (hp' : p' ∈ unipotentBall3 v c) :
    (p.1 + p'.1, p.2.1 + p'.2.1, p.2.2 + p'.2.2 + p.1 * p'.2.1) ∈ unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff] at hp hp' ⊢
  refine ⟨(Valuation.map_add _ _ _).trans (max_le hp.1 hp'.1),
    (Valuation.map_add _ _ _).trans (max_le hp.2.1 hp'.2.1), ?_⟩
  refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le hp.2.2 hp'.2.2)) ?_)
  rw [Valuation.map_mul, two_mul, WithZero.exp_add]
  exact mul_le_mul' hp.1 hp'.2.1

theorem unipotentBall3_inv_mem {c : ℤ} {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (hp : p ∈ unipotentBall3 v c) : (-p.1, -p.2.1, p.1 * p.2.1 - p.2.2) ∈ unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff] at hp ⊢
  refine ⟨by rw [Valuation.map_neg]; exact hp.1, by rw [Valuation.map_neg]; exact hp.2.1, ?_⟩
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ hp.2.2)
  rw [Valuation.map_mul, two_mul, WithZero.exp_add]
  exact mul_le_mul' hp.1 hp.2.1

theorem zero_mem_unipotentBall3 (c : ℤ) :
    ((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ)) ∈ unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff, Valuation.map_zero]
  exact ⟨zero_le', zero_le', zero_le'⟩

def jacquetHaar3 :
    @Measure (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)
      (@Prod.instMeasurableSpace _ _ (localBorel ℚ v)
        (@Prod.instMeasurableSpace _ _ (localBorel ℚ v) (localBorel ℚ v))) := by
  letI := localBorel ℚ v
  exact (selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))

theorem psiLoc_stdAddChar : psiLoc (stdAddChar ℚ) v = psiLocal ℚ v :=
  rfl

def jacquetTruncated3 (c : ℤ) (u : LocalGL3 v → ℂ) : ℂ := by
  letI := localBorel ℚ v
  exact ∫ p in unipotentBall3 v c,
    psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) ∂(jacquetHaar3 v)

theorem jacquetTruncated3_add (c : ℤ) (u u' : LocalGL3 v → ℂ)
    (hu : letI := localBorel ℚ v; IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
        (unipotentBall3 v c) (jacquetHaar3 v))
    (hu' : letI := localBorel ℚ v; IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u' (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
        (unipotentBall3 v c) (jacquetHaar3 v)) :
    jacquetTruncated3 v c (u + u') = jacquetTruncated3 v c u + jacquetTruncated3 v c u' := by
  letI := localBorel ℚ v
  simp only [jacquetTruncated3, Pi.add_apply, mul_add]
  exact integral_add hu hu'

theorem jacquetTruncated3_smul (c : ℤ) (a : ℂ) (u : LocalGL3 v → ℂ) :
    jacquetTruncated3 v c (a • u) = a * jacquetTruncated3 v c u := by
  letI := localBorel ℚ v
  simp only [jacquetTruncated3, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

def jacquetLevel (u : LocalGL3 v → ℂ) : ℕ :=
  sInf {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u}

def jacquetValue (u : LocalGL3 v → ℂ) : ℂ :=
  jacquetTruncated3 v (jacquetLevel v u) u

theorem jacquetTruncated3_eq_jacquetValue (u : LocalGL3 v → ℂ)
    (h : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u) {c : ℤ}
    (hc : (jacquetLevel v u : ℤ) ≤ c) : jacquetTruncated3 v c u = jacquetValue v u := by
  have hmem : jacquetLevel v u ∈
      {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u} :=
    Nat.sInf_mem h
  exact hmem c hc

theorem jacquetLevel_le (u : LocalGL3 v → ℂ) {c₀ : ℕ}
    (h : ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u) :
    jacquetLevel v u ≤ c₀ :=
  Nat.sInf_le h

def bigCell3 : Set (LocalGL3 v) :=
  {g | cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0}

theorem upperUnipotent3_mul_mem_bigCell3_iff (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    upperUnipotent3 x y z * g ∈ bigCell3 v ↔ g ∈ bigCell3 v := by
  simp only [bigCell3, Set.mem_setOf_eq, cornerEntry_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul]

theorem diagonal3_mul_mem_bigCell3_iff (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    diagonal3 v a * g ∈ bigCell3 v ↔ g ∈ bigCell3 v := by
  simp only [bigCell3, Set.mem_setOf_eq, cornerEntry_diagonal3_mul, lowerMinor_diagonal3_mul, ne_eq,
    mul_eq_zero, Units.ne_zero, false_or]

theorem mem_bigCell3_iff (g : LocalGL3 v) : g ∈ bigCell3 v ↔ cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0 :=
  Iff.rfl

theorem cellCutoff_subset_bigCell3 : cellCutoff v ⊆ bigCell3 v := by
  intro g h
  simp only [cellCutoff, Set.mem_setOf_eq] at h
  exact (mem_bigCell3_iff v g).mpr ⟨h.1, h.2.1⟩

def cellSectionOf (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    LocalGL3 v → ℂ :=
  (bigCell3 v).indicator fun g => cellValue v χ g * Φ (cellRatio v g)

theorem cellSectionOf_apply_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {g : LocalGL3 v} (hg : g ∈ bigCell3 v) :
    cellSectionOf v χ Φ g = cellValue v χ g * Φ (cellRatio v g) :=
  Set.indicator_of_mem hg _

theorem cellSectionOf_apply_of_notMem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {g : LocalGL3 v} (hg : g ∉ bigCell3 v) :
    cellSectionOf v χ Φ g = 0 :=
  Set.indicator_of_notMem hg _

theorem cellSectionOf_upperUnipotent3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    cellSectionOf v χ Φ (upperUnipotent3 x y z * g) = cellSectionOf v χ Φ g := by
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ ((upperUnipotent3_mul_mem_bigCell3_iff v x y z g).mpr hg),
      cellSectionOf_apply_of_mem v χ Φ hg, cellValue_upperUnipotent3_mul, cellRatio_upperUnipotent3_mul]
  · rw [cellSectionOf_apply_of_notMem v χ Φ (fun h => hg ((upperUnipotent3_mul_mem_bigCell3_iff v x y z g).mp h)),
      cellSectionOf_apply_of_notMem v χ Φ hg]

theorem cellSectionOf_diagonal3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    cellSectionOf v χ Φ (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * cellSectionOf v χ Φ g := by
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ ((diagonal3_mul_mem_bigCell3_iff v a g).mpr hg),
      cellSectionOf_apply_of_mem v χ Φ hg, cellValue_diagonal3_mul, cellRatio_diagonal3_mul]
    ring
  · rw [cellSectionOf_apply_of_notMem v χ Φ (fun h => hg ((diagonal3_mul_mem_bigCell3_iff v a g).mp h)),
      cellSectionOf_apply_of_notMem v χ Φ hg, mul_zero]

theorem cellSectionOf_indicator_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    cellSectionOf v χ (Set.indicator {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i) ≤ 1} 1) =
      cellSection v χ := by
  funext g
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ _ hg]
    by_cases hr : ∀ i, Valued.v (cellRatio v g i) ≤ 1
    · have hc : g ∈ cellCutoff v := by
        have hg' := (mem_bigCell3_iff v g).mp hg
        simp only [cellCutoff, Set.mem_setOf_eq]
        exact ⟨hg'.1, hg'.2, hr⟩
      rw [cellSection, Set.indicator_of_mem hc,
        Set.indicator_of_mem (show cellRatio v g ∈ {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i) ≤ 1}
          from hr), Pi.one_apply, mul_one]
    · have hc : g ∉ cellCutoff v := fun h => hr (by simp only [cellCutoff, Set.mem_setOf_eq] at h; exact h.2.2)
      rw [cellSection, Set.indicator_of_notMem hc,
        Set.indicator_of_notMem (show cellRatio v g ∉ {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i) ≤ 1}
          from hr), mul_zero]
  · have hc : g ∉ cellCutoff v := fun h => hg (cellCutoff_subset_bigCell3 v h)
    rw [cellSectionOf_apply_of_notMem v χ _ hg, cellSection, Set.indicator_of_notMem hc]

def jacquetWhittaker3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    LocalGL3 v → ℂ :=
  fun g => jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ))

theorem jacquetWhittaker3_apply (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) :
    jacquetWhittaker3 v χ Φ g = jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ)) :=
  rfl

end Jacquet

end LanglandsTunnell.CubicInduction

end


