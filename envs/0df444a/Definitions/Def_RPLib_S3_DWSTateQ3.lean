-- Prove2me | Definitions.Def_RPLib_S3_DWSTateQ3
-- name    : RPLib_S3_DWSTateQ3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:22:55.234886+00:00
-- url     : https://prove2.me/theorems/a40f6bde-50b4-4574-9f4e-2c9e6ac93419
-- title:
--   Weight-two Ramanujan-Petersson library: form classes and ideal classes (`f ~ g ⇔ [I_f] = [I_g]`)
-- statement:
--   Form classes and ideal classes (`f ~ g ⇔ [I_f] = [I_g]`).
--
--   Pure algebra. `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
--   * `IdealRel I J`: `(α) I = (β) J` for nonzero `α, β` (equality of ideal classes); refl/symm/trans.
--   * `formIdeal f = (f.a, ω - k_f)`, `k_f = (b + f.b) / 2`; `two_mul_kf`, `kf_rel`, `formIdeal_eq_lat`, `mem_formIdeal`,
--     `hasForm_canon` (the pair `(f.a, ω - k_f)` has the form `f`).
--   * **`idealRel_act`**: `[I_f] = [I_{γ f}]`; **`exists_act_of_idealRel`**: `[I_f] = [I_g] ⇒ g = act γ f`;
--     `idealRel_iff_mem_orbit` (for primitive positive definite forms of discriminant `D`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateQ2
import Definitions.Def_RPLib_S3_HurwitzB

/-!
# S3-DWS-Tate, part Q3: form classes and ideal classes (`f ~ g ⇔ [I_f] = [I_g]`)

Pure algebra. `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
* `IdealRel I J`: `(α) I = (β) J` for nonzero `α, β` (equality of ideal classes); refl/symm/trans.
* `formIdeal f = (f.a, ω - k_f)`, `k_f = (b + f.b) / 2`; `two_mul_kf`, `kf_rel`, `formIdeal_eq_lat`, `mem_formIdeal`,
  `hasForm_canon` (the pair `(f.a, ω - k_f)` has the form `f`).
* **`idealRel_act`**: `[I_f] = [I_{γ f}]`; **`exists_act_of_idealRel`**: `[I_f] = [I_g] ⇒ g = act γ f`;
  `idealRel_iff_mem_orbit` (for primitive positive definite forms of discriminant `D`).
-/

set_option autoImplicit false

namespace RPLib.DWS.QA

open QuadraticAlgebra RamanujanPetersson.Hurwitz MatrixGroups

variable {a b : ℤ}

/-- `(α) I = (β) J` for some nonzero `α, β`. -/
def IdealRel (I J : Ideal (QuadraticAlgebra ℤ a b)) : Prop :=
  ∃ α β : QuadraticAlgebra ℤ a b, α ≠ 0 ∧ β ≠ 0 ∧ Ideal.span {α} * I = Ideal.span {β} * J

theorem IdealRel.refl (I : Ideal (QuadraticAlgebra ℤ a b)) : IdealRel I I :=
  ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

theorem IdealRel.symm {I J : Ideal (QuadraticAlgebra ℤ a b)} (h : IdealRel I J) : IdealRel J I := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  exact ⟨β, α, hβ, hα, h.symm⟩

theorem IdealRel.trans (hD : b ^ 2 + 4 * a < 0) {I J K : Ideal (QuadraticAlgebra ℤ a b)}
    (h : IdealRel I J) (h' : IdealRel J K) : IdealRel I K := by
  haveI := noZeroDivisors hD
  obtain ⟨α, β, hα, hβ, h⟩ := h
  obtain ⟨γ, δ, hγ, hδ, h'⟩ := h'
  refine ⟨γ * α, β * δ, mul_ne_zero hγ hα, mul_ne_zero hβ hδ, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, h, ← mul_assoc,
    mul_comm (Ideal.span {γ}), mul_assoc, h', ← mul_assoc, Ideal.span_singleton_mul_span_singleton]

theorem intCast_ne_zero' {n : ℤ} (hn : n ≠ 0) : (n : QuadraticAlgebra ℤ a b) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [re_intCast, re_zero] at this
  exact hn this

theorem mul_lin (z : QuadraticAlgebra ℤ a b) (p r : ℤ) (x y : QuadraticAlgebra ℤ a b) :
    z * lin p r x y = lin p r (z * x) (z * y) := by
  ext <;> simp only [lin, re_mul, im_mul] <;> ring

/-- The ideal `ℤ A + ℤ (ω - k)` of the form `f = (A, B, C)`, `k = (b + B) / 2`. -/
def formIdeal (f : BQF) : Ideal (QuadraticAlgebra ℤ a b) :=
  Ideal.span {(f.a : QuadraticAlgebra ℤ a b), ⟨-((b + f.b) / 2), 1⟩}

theorem two_mul_kf {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) : 2 * ((b + f.b) / 2) = b + f.b := by
  have h4 : (f.b - b) * (f.b + b) = 2 * (2 * (a + f.a * f.c)) := by
    unfold BQF.disc at hf; linear_combination hf
  have hev : Even ((f.b - b) * (f.b + b)) := ⟨2 * (a + f.a * f.c), by rw [h4]; ring⟩
  have hb : Even (b + f.b) := by
    rcases Int.even_mul.mp hev with h | h
    · have e : b + f.b = (f.b - b) + 2 * b := by ring
      rw [e]; exact h.add (even_two_mul b)
    · rwa [add_comm]
  exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp hb)

theorem kf_rel {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) :
    a + (b + f.b) / 2 * b - ((b + f.b) / 2) ^ 2 = -(f.a * f.c) := by
  have hk := two_mul_kf hf
  unfold BQF.disc at hf
  apply mul_left_cancel₀ (four_ne_zero : (4 : ℤ) ≠ 0)
  linear_combination (-(f.b + 2 * ((b + f.b) / 2) - b)) * hk - hf

theorem kf_dvd {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) :
    f.a ∣ a + (b + f.b) / 2 * b - ((b + f.b) / 2) ^ 2 :=
  ⟨-f.c, by rw [kf_rel hf]; ring⟩

theorem formIdeal_eq_lat {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) :
    (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) = lat f.a ((b + f.b) / 2) (kf_dvd hf) :=
  (lat_eq_span (hk := kf_dvd hf)).symm

theorem mem_formIdeal {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) {z : QuadraticAlgebra ℤ a b} :
    z ∈ formIdeal f ↔ ∃ m n : ℤ, z = lin m n (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩ := by
  rw [formIdeal_eq_lat hf, mem_lat_iff_exists]
  simp only [lin_eq]

theorem hasForm_canon {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) :
    HasForm (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩ f := by
  have h := hasForm_lat (a := a) (b := b) (A := f.a) (k := (b + f.b) / 2) (C := f.c) (kf_rel hf)
  have e : (⟨f.a, 2 * ((b + f.b) / 2) - b, f.c⟩ : BQF) = f :=
    BQF.ext rfl (by show 2 * ((b + f.b) / 2) - b = f.b; rw [two_mul_kf hf]; ring) rfl
  rwa [e] at h

theorem span_pair_mul (u v w : QuadraticAlgebra ℤ a b) :
    Ideal.span {u} * Ideal.span {v, w} = Ideal.span {u * v, u * w} := by
  rw [Ideal.span_mul_span', Set.singleton_mul, Set.image_pair]

theorem lin_mem_span (p r : ℤ) (x y : QuadraticAlgebra ℤ a b) : lin p r x y ∈ Ideal.span {x, y} := by
  rw [lin_eq]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))

theorem span_pair_eq {x y x' y' : QuadraticAlgebra ℤ a b} {m1 m2 m3 m4 n1 n2 n3 n4 : ℤ}
    (hx' : x' = lin m1 m2 x y) (hy' : y' = lin m3 m4 x y) (hx : x = lin n1 n2 x' y')
    (hy : y = lin n3 n4 x' y') : Ideal.span {x, y} = Ideal.span {x', y'} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz, hx]; exact lin_mem_span _ _ _ _
    · rw [Set.mem_singleton_iff.mp hz, hy]; exact lin_mem_span _ _ _ _
  · rw [Ideal.span_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz, hx']; exact lin_mem_span _ _ _ _
    · rw [Set.mem_singleton_iff.mp hz, hy']; exact lin_mem_span _ _ _ _

/-- **`[I_f] = [I_{γ f}]`.** -/
theorem idealRel_act {f : BQF} (hf : f ∈ primForms (b ^ 2 + 4 * a)) (γ : SL(2, ℤ)) :
    IdealRel (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) (formIdeal (act γ f)) := by
  have hfd : f.disc = b ^ 2 + 4 * a := hf.1
  have hgd : (act γ f).disc = b ^ 2 + 4 * a := (disc_act γ f).trans hfd
  have hga : 0 < (act γ f).a := (posDef_act_of γ hf.2.1).1
  have hd := RamanujanPetersson.Hurwitz.det_eq γ
  have h' := (hasForm_canon (a := a) hfd).act γ
  have hg := hasForm_canon (a := a) hgd
  have hdt : dt (lin (γ 0 0) (-γ 1 0) (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩)
      (lin (-γ 0 1) (γ 1 1) (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩) = f.a := by
    rw [dt_lin, dt_lat]; linear_combination f.a * hd
  have key := h'.mul_eq hg (ne_of_gt hga) (by rw [hdt]; exact ne_of_gt hf.2.1.1)
    (by rw [dt_lat]; exact ne_of_gt hga)
  have hspan : (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) =
      Ideal.span {lin (γ 0 0) (-γ 1 0) (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩,
        lin (-γ 0 1) (γ 1 1) (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩} := by
    refine span_pair_eq rfl rfl (n1 := γ 1 1) (n2 := γ 1 0) (n3 := γ 0 1) (n4 := γ 0 0) ?_ ?_
    · ext
      · simp only [lin]; linear_combination (-(f.a : QuadraticAlgebra ℤ a b).re) * hd
      · simp only [lin]; linear_combination (-(f.a : QuadraticAlgebra ℤ a b).im) * hd
    · ext
      · simp only [lin]; linear_combination ((b + f.b) / 2) * hd
      · simp only [lin]; linear_combination (-1 : ℤ) * hd
  set x' := lin (γ 0 0) (-γ 1 0) (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩ with hx'
  set y' := lin (-γ 0 1) (γ 1 1) (f.a : QuadraticAlgebra ℤ a b) ⟨-((b + f.b) / 2), 1⟩ with hy'
  set Ag : QuadraticAlgebra ℤ a b := ((act γ f).a : QuadraticAlgebra ℤ a b) with hAg
  set Yg : QuadraticAlgebra ℤ a b := ⟨-((b + (act γ f).b) / 2), 1⟩ with hYg
  refine ⟨Ag, x', intCast_ne_zero' (ne_of_gt hga), ?_, ?_⟩
  · intro h0
    have h1 := h'.1
    rw [hdt, h0, QuadraticAlgebra.norm_zero] at h1
    exact (mul_pos hf.2.1.1 hga).ne h1
  · rw [hspan]
    show Ideal.span {Ag} * Ideal.span {x', y'} = Ideal.span {x'} * Ideal.span {Ag, Yg}
    rw [span_pair_mul, span_pair_mul, mul_comm Ag x', mul_comm Ag y', key, mul_comm Yg x']

theorem exists_lin_of_mem {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) {α w : QuadraticAlgebra ℤ a b}
    (hw : w ∈ Ideal.span {α} * formIdeal f) :
    ∃ m n : ℤ, w = lin m n (α * (f.a : QuadraticAlgebra ℤ a b)) (α * ⟨-((b + f.b) / 2), 1⟩) := by
  obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.mp hw
  obtain ⟨m, n, rfl⟩ := (mem_formIdeal hf).mp hz
  exact ⟨m, n, mul_lin _ _ _ _ _⟩

/-- **`[I_f] = [I_g] ⇒ g = act γ f`** for primitive positive definite forms of discriminant `D < 0`. -/
theorem exists_act_of_idealRel (hD : b ^ 2 + 4 * a < 0) {f g : BQF}
    (hf : f ∈ primForms (b ^ 2 + 4 * a)) (hg : g ∈ primForms (b ^ 2 + 4 * a))
    (h : IdealRel (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) (formIdeal g)) :
    ∃ γ : SL(2, ℤ), act γ f = g := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  have hP := (hasForm_canon (a := a) hf.1).mul α
  have hQ := (hasForm_canon (a := a) hg.1).mul β
  have dP : 0 < dt (α * (f.a : QuadraticAlgebra ℤ a b)) (α * ⟨-((b + f.b) / 2), 1⟩) := by
    rw [dt_mul, dt_lat]; exact mul_pos (norm_pos hD hα) hf.2.1.1
  have dQ : 0 < dt (β * (g.a : QuadraticAlgebra ℤ a b)) (β * ⟨-((b + g.b) / 2), 1⟩) := by
    rw [dt_mul, dt_lat]; exact mul_pos (norm_pos hD hβ) hg.2.1.1
  have mQ : ∀ z ∈ (formIdeal g : Ideal (QuadraticAlgebra ℤ a b)),
      β * z ∈ Ideal.span {α} * formIdeal f := fun z hz => by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self β) hz
  have mP : ∀ z ∈ (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)),
      α * z ∈ Ideal.span {β} * formIdeal g := fun z hz => by
    rw [← h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self α) hz
  obtain ⟨m1, m2, e1⟩ := exists_lin_of_mem hf.1 (mQ _ (Ideal.subset_span (Set.mem_insert _ _)))
  obtain ⟨m3, m4, e2⟩ := exists_lin_of_mem hf.1
    (mQ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  obtain ⟨n1, n2, e3⟩ := exists_lin_of_mem hg.1 (mP _ (Ideal.subset_span (Set.mem_insert _ _)))
  obtain ⟨n3, n4, e4⟩ := exists_lin_of_mem hg.1
    (mP _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  have hdet := det_eq_one_of_bases e1 e2 e3 e4 dP dQ
  obtain ⟨γ, g00, g01, g10, g11⟩ : ∃ γ : SL(2, ℤ), γ 0 0 = m1 ∧ γ 0 1 = -m3 ∧ γ 1 0 = -m2 ∧
      γ 1 1 = m4 :=
    ⟨⟨!![m1, -m3; -m2, m4], by rw [Matrix.det_fin_two_of]; linear_combination hdet⟩,
      rfl, rfl, rfl, rfl⟩
  have hγ := hP.act γ
  rw [g00, g01, g10, g11, neg_neg, neg_neg, ← e1, ← e2] at hγ
  exact ⟨γ, hγ.unique hQ (ne_of_gt dQ)⟩

/-- **(d3)** For primitive positive definite forms of discriminant `D = b² + 4a < 0`:
`[I_f] = [I_g]` iff `f` and `g` are `SL(2, ℤ)`-equivalent. -/
theorem idealRel_iff (hD : b ^ 2 + 4 * a < 0) {f g : BQF}
    (hf : f ∈ primForms (b ^ 2 + 4 * a)) (hg : g ∈ primForms (b ^ 2 + 4 * a)) :
    IdealRel (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) (formIdeal g) ↔
      ∃ γ : SL(2, ℤ), act γ f = g := by
  constructor
  · exact exists_act_of_idealRel hD hf hg
  · rintro ⟨γ, rfl⟩; exact idealRel_act hf γ

end RPLib.DWS.QA


