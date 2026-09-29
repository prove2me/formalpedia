-- Prove2me | Definitions.Def_NumberField_IdeleBox
-- name    : NumberField_IdeleBox
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/e93bd644-33a5-5803-89b1-e96bcb2db87a
-- title:
--   Idèle boxes: local-condition subgroups of unit idèle groups
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$ (a commutative ring with the Dedekind property, $K$ a field that is an $R$-algebra and a fraction field of $R$). For the finite adèles, [`IsDedekindDomain.FiniteAdeleRing.unitsComponent`](../def/NumberField_IdeleBox.html#L10) is the monoid homomorphism $(\mathbb{A}_K^f)^\times \to (K_v)^\times$ obtained by applying `Units.map` to evaluation at a height-one prime $v$, and two companion lemmas identify the underlying element of $K_v$ of the $v$-component of $x$ and of $x^{-1}$ with the $v$-entries of the corresponding finite adèles. The lemma `integer_and_inv_integer_iff_valuation_eq_one` is the bridge between two spellings of "unit at $v$": for a unit $x$ of the finite adèle ring, $x_v$ and $(x^{-1})_v$ both lie in $v.adicCompletionIntegers K$ if and only if $\mathrm{v}(x_v) = 1$. The main definition [`IsDedekindDomain.FiniteAdeleRing.ideleBox`](../def/NumberField_IdeleBox.html#L48) takes a set $S$ of height-one primes and a family of subgroups $H_v \le (K_v)^\times$ indexed by all height-one primes, and forms the subgroup of $(\mathbb{A}_K^f)^\times$ consisting of those $x$ with $x$-component in $H_v$ for every $v \in S$ and, for $v \notin S$, with both $x_v$ and $(x^{-1})_v$ integral at $v$. Its membership criterion holds by definition; the box is monotone in the family $H$ restricted to $S$, is contained in `unitIdelesOutside R K S`, and equals that group when $H$ is taken to be the top subgroup everywhere.
--
--   The second half transfers this to the full adèle ring $\mathbb{A}_K = \mathbb{A}_K^\infty \times \mathbb{A}_K^f$: `finitePartUnits` is the homomorphism on units induced by the projection onto the finite factor, `finiteUnitsComponent` is its composition with `unitsComponent` at $v$, and `infiniteUnitsComponent` is induced by projection to the infinite factor followed by evaluation at an infinite place $w$, landing in $(w.Completion)^\times$; identification lemmas record the underlying values. [`NumberField.AdeleRing.ideleBox`](../def/NumberField_IdeleBox.html#L126) then takes $S$, a family $H_v$ of subgroups of $(K_v)^\times$ and a family $H_w$ of subgroups of $(w.Completion)^\times$, and cuts out the units $x$ of $\mathbb{A}_K$ whose finite part lies in the finite idèle box and whose $w$-component lies in $H_w$ for every infinite place $w$. The unfolded membership criterion, monotonicity in both families, the identification of the doubly-top box with `unitIdelesOutside R K S`, and containment in the latter for arbitrary families are recorded.
--
--   **Relation to Mathlib.** Mathlib supplies the finite adèle ring as a restricted product, the adic completions `HeightOneSpectrum.adicCompletion` with their valuation rings `adicCompletionIntegers`, the adèle ring of a Dedekind domain and the completions at infinite places; the idèle box subgroups themselves, like the `unitIdelesOutside` subgroups they refine, are the project's own constructions.
--
--   **Where it is used.** These subgroups provide the language of local conditions on idèles — arbitrary constraints at a finite set $S$ of finite places and at the infinite places, combined with the requirement of being a unit at all remaining finite places — in which the idelic and class-field-theoretic inputs to the argument are phrased.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_IdeleBox.lean

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def unitsComponent (v : HeightOneSpectrum R) :
    (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom
    (fun v : HeightOneSpectrum R => v.adicCompletion K) v).toMonoidHom

variable {R K} in
@[simp]
theorem val_unitsComponent (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    ((unitsComponent R K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : FiniteAdeleRing R K) v :=
  rfl

variable {R K} in
theorem val_inv_unitsComponent (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    (((unitsComponent R K v x)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v :=
  rfl

variable {R K} in

theorem integer_and_inv_integer_iff_valuation_eq_one (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    ((x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K)
      ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hmul : (x : FiniteAdeleRing R K) v * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
    rw [← val_unitsComponent, ← val_inv_unitsComponent, Units.mul_inv]
  have hab : Valued.v ((x : FiniteAdeleRing R K) v)
      * Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, hmul, map_one]
  have ha0 : Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 := left_ne_zero_of_mul_eq_one hab
  rw [← inv_eq_of_mul_eq_one_right hab]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 ha0)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

def ideleBox (S : Set (HeightOneSpectrum R)) (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) :
    Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {x | (∀ v ∈ S, unitsComponent R K v x ∈ H v) ∧
    ∀ v : HeightOneSpectrum R, v ∉ S →
      (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' := ⟨fun v _ => by rw [map_one]; exact one_mem _,
    fun v _ => ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv => by rw [map_mul]; exact mul_mem (hx1 v hv) (hy1 v hv), fun v hv => ?_⟩
    obtain ⟨hx, hx'⟩ := hx2 v hv
    obtain ⟨hy, hy'⟩ := hy2 v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx hy, by rw [mul_inv, Units.val_mul]; exact mul_mem hx' hy'⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun v hv => by rw [map_inv]; exact inv_mem (hx1 v hv),
      fun v hv => ⟨(hx2 v hv).2, by rw [inv_inv]; exact (hx2 v hv).1⟩⟩

variable {R K} in
theorem mem_ideleBox_iff (S : Set (HeightOneSpectrum R))
    (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) (x : (FiniteAdeleRing R K)ˣ) :
    x ∈ ideleBox R K S H ↔
      (∀ v ∈ S, unitsComponent R K v x ∈ H v) ∧
        ∀ v : HeightOneSpectrum R, v ∉ S →
          (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
            ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem ideleBox_mono {S : Set (HeightOneSpectrum R)}
    {H H' : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ} (h : ∀ v ∈ S, H v ≤ H' v) :
    ideleBox R K S H ≤ ideleBox R K S H' :=
  fun _ hx => ⟨fun v hv => h v hv (hx.1 v hv), hx.2⟩

theorem ideleBox_top (S : Set (HeightOneSpectrum R)) : ideleBox R K S ⊤ = unitIdelesOutside R K S :=
  Subgroup.ext fun _ => ⟨fun h => h.2, fun h => ⟨fun _ _ => Subgroup.mem_top _, h⟩⟩

theorem ideleBox_le_unitIdelesOutside (S : Set (HeightOneSpectrum R))
    (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) :
    ideleBox R K S H ≤ unitIdelesOutside R K S :=
  fun _ hx => hx.2

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def finitePartUnits : (AdeleRing R K)ˣ →* (IsDedekindDomain.FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom

variable {R K} in
@[simp]
theorem val_finitePartUnits (x : (AdeleRing R K)ˣ) :
    ((finitePartUnits R K x : (IsDedekindDomain.FiniteAdeleRing R K)ˣ) : IsDedekindDomain.FiniteAdeleRing R K)
      = (x : AdeleRing R K).2 :=
  rfl

noncomputable def finiteUnitsComponent (v : IsDedekindDomain.HeightOneSpectrum R) :
    (AdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitsComponent R K v).comp (finitePartUnits R K)

noncomputable def infiniteUnitsComponent (w : InfinitePlace K) : (AdeleRing R K)ˣ →* (w.Completion)ˣ :=
  Units.map ((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K))).toMonoidHom

variable {R K} in
@[simp]
theorem val_finiteUnitsComponent (v : IsDedekindDomain.HeightOneSpectrum R) (x : (AdeleRing R K)ˣ) :
    ((finiteUnitsComponent R K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : AdeleRing R K).2 v :=
  rfl

variable {R K} in
@[simp]
theorem val_infiniteUnitsComponent (w : InfinitePlace K) (x : (AdeleRing R K)ˣ) :
    ((infiniteUnitsComponent R K w x : (w.Completion)ˣ) : w.Completion) = (x : AdeleRing R K).1 w :=
  rfl

def ideleBox (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) : Subgroup (AdeleRing R K)ˣ where
  carrier := {x | finitePartUnits R K x ∈ IsDedekindDomain.FiniteAdeleRing.ideleBox R K S H ∧
    ∀ w : InfinitePlace K, infiniteUnitsComponent R K w x ∈ Hinf w}
  one_mem' := ⟨by rw [map_one]; exact one_mem _, fun w => by rw [map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_mul]; exact mul_mem hx1 hy1, fun w => by rw [map_mul]; exact mul_mem (hx2 w) (hy2 w)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [map_inv]; exact inv_mem hx1, fun w => by rw [map_inv]; exact inv_mem (hx2 w)⟩

variable {R K} in

theorem mem_ideleBox_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) (x : (AdeleRing R K)ˣ) :
    x ∈ ideleBox R K S H Hinf ↔
      ((∀ v ∈ S, finiteUnitsComponent R K v x ∈ H v) ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum R, v ∉ S →
          (x : AdeleRing R K).2 v ∈ v.adicCompletionIntegers K ∧
            ((x⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K).2 v ∈ v.adicCompletionIntegers K) ∧
      ∀ w : InfinitePlace K, infiniteUnitsComponent R K w x ∈ Hinf w :=
  Iff.rfl

theorem ideleBox_mono {S : Set (IsDedekindDomain.HeightOneSpectrum R)}
    {H H' : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ}
    {Hinf Hinf' : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ}
    (h : ∀ v ∈ S, H v ≤ H' v) (hinf : ∀ w, Hinf w ≤ Hinf' w) :
    ideleBox R K S H Hinf ≤ ideleBox R K S H' Hinf' :=
  fun _ hx => ⟨IsDedekindDomain.FiniteAdeleRing.ideleBox_mono R K h hx.1, fun w => hinf w (hx.2 w)⟩

theorem ideleBox_top_top (S : Set (IsDedekindDomain.HeightOneSpectrum R)) :
    ideleBox R K S ⊤ ⊤ = unitIdelesOutside R K S :=
  Subgroup.ext fun _ =>
    ⟨fun h => (IsDedekindDomain.FiniteAdeleRing.ideleBox_top R K S).le h.1,
      fun h => ⟨(IsDedekindDomain.FiniteAdeleRing.ideleBox_top R K S).ge h, fun _ => Subgroup.mem_top _⟩⟩

theorem ideleBox_le_unitIdelesOutside (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) :
    ideleBox R K S H Hinf ≤ unitIdelesOutside R K S :=
  fun _ hx => IsDedekindDomain.FiniteAdeleRing.ideleBox_le_unitIdelesOutside R K S H hx.1

end NumberField.AdeleRing


