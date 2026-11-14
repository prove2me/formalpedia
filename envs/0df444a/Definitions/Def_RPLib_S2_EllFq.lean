-- Prove2me | Definitions.Def_RPLib_S2_EllFq
-- name    : RPLib_S2_EllFq
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:50:41.464817+00:00
-- url     : https://prove2.me/theorems/14e20211-fdb6-4e9e-80d1-b1b324d2dd64
-- title:
--   Point counts of elliptic curves over finite fields, base change and the Frobenius on points
-- statement:
--   For a Weierstrass curve $W$ over a finite field $\mathbb{F}_q$: finiteness of $W(\mathbb{F}_q)$, the trace $a = q + 1 - \#W(\mathbb{F}_q)$ and its link to Mathlib's local factor $1 - aT + qT^2$, base change of points, and the $q$-power Frobenius on $W(K)$ for $K \supseteq \mathbb{F}_q$ algebraically closed, whose fixed points are $W(\mathbb{F}_{q^m})$ for its $m$-th power.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Sections V.1 and V.2

import Mathlib

/-!
# Elliptic curves over finite fields: point counts, base change, Frobenius on points

Library unit S2-EllFq of the Ramanujan-Petersson project (Mathlib-only imports).

## Main definitions and results

* `RPLib.EllFq.finite_point`, `RPLib.EllFq.fintypePoint` : `W(F)` is finite for finite `F`
  (stated as a theorem / def, used as local instances: platform convention forbids global instances).
* `RPLib.EllFq.numPoints W` : `N(W/F) = Nat.card W(F)` (the point at infinity included).
* `RPLib.EllFq.trace W` : `a(W) = q + 1 - N(W/F)` as an integer;
  `localPolynomial_eq_of_hasGoodReduction` : it is the `a` in `WeierstrassCurve.localPolynomial`.
* `RPLib.EllFq.baseChangePt W K` : the injective group map `W(F) → W(K)`; `mapPt`, `mapPtEquiv`.
* `RPLib.EllFq.frob W K` : the `q`-power Frobenius on `W(K)` for any extension `K / F`
  (an additive endomorphism; `frobAut` an additive automorphism when `K / F` is algebraic, e.g. an
  algebraic closure).
  - `frob_eq_self_iff` : fixed points are exactly the image of `W(F)`;
  - `frob_iterate_eq_self_iff` : `Frob^m` fixes exactly the image of `W(L)` for any intermediate
    field `F ⊆ L ⊆ K` with `#L = q ^ m`;
  - `powFixedField K m` : the subfield `{x | x ^ (q ^ m) = x}`, of cardinality `q ^ m` when `K` is
    algebraically closed and `m ≠ 0` (`card_powFixedField`), and
    `frob_iterate_eq_self_iff_powFixedField` : `Frob^m` fixes exactly `W(𝔽_{q^m})`;
  - `numPoints_eq_card_fixed`, `numPoints_baseChange_eq_card_fixed`,
    `numPoints_powFixedField_eq_card_fixed` : point counts as fixed-point counts.
* `RPLib.EllFq.numPoints_variableChange`, `trace_variableChange` : invariance under
  `WeierstrassCurve.VariableChange` (for elliptic curves).
* Sanity checks: `y² = x³ + 1` over `𝔽₅` has `N = 6`, `a = 0`; `y² = x³ + x + 1` over `𝔽₅` has
  `N = 9`, `a = -3` (by `decide`, no native evaluation).
-/

set_option autoImplicit false

open Polynomial

namespace RPLib.EllFq

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## Finiteness and point counts -/

/-- Injection of the points of `W` into `Option (F × F)`. -/
def pointToOption {F : Type*} [Field F] (W : WeierstrassCurve F) :
    W.toAffine.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

lemma pointToOption_injective {F : Type*} [Field F] (W : WeierstrassCurve F) :
    Function.Injective (pointToOption W) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ <;> simp_all [pointToOption]

/-- `W(F)` is finite for a finite field `F`. (Not a global instance, per platform convention:
downstream files use `attribute [local instance] RPLib.EllFq.finite_point`.) -/
theorem finite_point {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) :
    Finite W.toAffine.Point :=
  Finite.of_injective _ (pointToOption_injective W)

/-- A `Fintype` structure on `W(F)` for a finite field `F` (use as a local instance). -/
@[instance_reducible]
noncomputable def fintypePoint {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) :
    Fintype W.toAffine.Point :=
  have := finite_point W
  Fintype.ofFinite _

attribute [local instance] finite_point fintypePoint

section Count

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- `N(W/F)`: the number of points of `W` over `F`, including the point at infinity. -/
noncomputable def numPoints : ℕ := Nat.card W.toAffine.Point

/-- `a(W) = q + 1 - N(W/F)` with `q = #F`. -/
noncomputable def trace : ℤ := (Nat.card F : ℤ) + 1 - (numPoints W : ℤ)

lemma numPoints_eq_fintype_card [Finite F] : numPoints W = Fintype.card W.toAffine.Point :=
  Nat.card_eq_fintype_card

lemma numPoints_pos [Finite F] : 0 < numPoints W :=
  Nat.card_pos

/-- `N = 1 + #{nonsingular affine solutions}`. -/
lemma numPoints_eq_card_nonsingular [Finite F] :
    numPoints W = Nat.card {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} + 1 := by
  rw [numPoints, Nat.card_congr (nonsingularPointEquiv W.toAffine)]
  exact Finite.card_option

/-- For an elliptic curve, `N = 1 + #{affine solutions of the Weierstrass equation}`. -/
lemma numPoints_eq_card_equation [Finite F] [W.IsElliptic] :
    numPoints W = Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
  rw [numPoints, Nat.card_congr (pointEquiv W.toAffine)]
  exact Finite.card_option

/-- Point count as an explicit finset count (used for computations). -/
lemma numPoints_eq_card_filter [Fintype F] [DecidableEq F] [W.IsElliptic] :
    numPoints W = (Finset.univ.filter (fun xy : F × F =>
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card + 1 := by
  rw [numPoints_eq_card_equation]
  have e : {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃ {xy : F × F //
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆} :=
    Equiv.subtypeEquivRight fun xy => equation_iff ..
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma trace_eq [Fintype F] : trace W = (Fintype.card F : ℤ) + 1 - (numPoints W : ℤ) := by
  rw [trace, Nat.card_eq_fintype_card]

lemma numPoints_eq_sub_trace : (numPoints W : ℤ) = (Nat.card F : ℤ) + 1 - trace W := by
  rw [trace]; ring

end Count

/-! ## Link with Mathlib's local polynomial -/

section LocalPolynomial

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

/-- At good reduction, Mathlib's local polynomial is `1 - a T + q T ^ 2` with `a = trace` of the
reduced curve over the residue field and `q` the cardinality of the residue field. -/
theorem localPolynomial_eq_of_hasGoodReduction (h : (W.minimal R).HasGoodReduction R) :
    W.localPolynomial R = 1 - C (trace ((W.minimal R).reduction R)) * X +
      C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  rw [localPolynomial, if_pos h]
  rfl

end LocalPolynomial

/-! ## Base change and maps of points -/

section BaseChange

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The map `W(F) → W(K)` for a field extension `K / F`. -/
noncomputable def baseChangePt [DecidableEq F] (K : Type*) [Field K] [DecidableEq K]
    [Algebra F K] : W.toAffine.Point →+ (W.baseChange K).toAffine.Point :=
  Affine.Point.baseChange (W' := W.toAffine) F K

lemma baseChangePt_zero [DecidableEq F] (K : Type*) [Field K] [DecidableEq K] [Algebra F K] :
    baseChangePt W K 0 = 0 := rfl

lemma baseChangePt_some [DecidableEq F] (K : Type*) [Field K] [DecidableEq K] [Algebra F K]
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange K).toAffine.Nonsingular (algebraMap F K x) (algebraMap F K y),
      baseChangePt W K (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

lemma baseChangePt_injective [DecidableEq F] (K : Type*) [Field K] [DecidableEq K]
    [Algebra F K] : Function.Injective (baseChangePt W K) :=
  Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId F K)

/-- `N(W/F) ≤ N(W/K)` for a finite extension. -/
lemma numPoints_le_baseChange [DecidableEq F] (K : Type*) [Field K] [DecidableEq K] [Algebra F K]
    [Finite K] : numPoints W ≤ numPoints (W.baseChange K) :=
  Nat.card_le_card_of_injective _ (baseChangePt_injective W K)

variable {K K' K'' : Type*} [Field K] [Field K'] [Field K''] [DecidableEq K] [DecidableEq K']
  [DecidableEq K''] [Algebra F K] [Algebra F K'] [Algebra F K'']

/-- Map of points along an `F`-algebra map between two extensions. -/
noncomputable def mapPt (f : K →ₐ[F] K') :
    (W.baseChange K).toAffine.Point →+ (W.baseChange K').toAffine.Point :=
  Affine.Point.map (W' := W.toAffine) f

lemma mapPt_injective (f : K →ₐ[F] K') : Function.Injective (mapPt W f) :=
  Affine.Point.map_injective (W' := W.toAffine) f

lemma mapPt_baseChangePt [DecidableEq F] (f : K →ₐ[F] K') (P : W.toAffine.Point) :
    mapPt W f (baseChangePt W K P) = baseChangePt W K' P :=
  Affine.Point.map_baseChange (W' := W.toAffine) f P

lemma mapPt_id (P : (W.baseChange K).toAffine.Point) : mapPt W (AlgHom.id F K) P = P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

lemma mapPt_comp (f : K →ₐ[F] K') (g : K' →ₐ[F] K'') (P : (W.baseChange K).toAffine.Point) :
    mapPt W g (mapPt W f P) = mapPt W (g.comp f) P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

/-- An `F`-algebra isomorphism of extensions induces an additive isomorphism of points. -/
noncomputable def mapPtEquiv (σ : K ≃ₐ[F] K') :
    (W.baseChange K).toAffine.Point ≃+ (W.baseChange K').toAffine.Point where
  toFun := mapPt W σ.toAlgHom
  invFun := mapPt W σ.symm.toAlgHom
  left_inv P := by
    rw [mapPt_comp (K'' := K)]
    convert mapPt_id W P
    ext x; simp
  right_inv P := by
    rw [mapPt_comp (K'' := K')]
    convert mapPt_id W P
    ext x; simp
  map_add' := (mapPt W σ.toAlgHom).map_add

lemma mapPtEquiv_apply (σ : K ≃ₐ[F] K') (P : (W.baseChange K).toAffine.Point) :
    mapPtEquiv W σ P = mapPt W σ.toAlgHom P := rfl

end BaseChange

/-! ## Fixed points of power maps -/

section Fixed

/-- In any extension `K` of a finite field `L`, the solutions of `x ^ #L = x` are exactly `L`. -/
lemma pow_card_eq_self_iff {L K : Type*} [Field L] [Fintype L] [Field K] [Algebra L K] (x : K) :
    x ^ Fintype.card L = x ↔ x ∈ (algebraMap L K).range := by
  constructor
  · intro hx
    by_contra hne
    classical
    let e : L ↪ K := ⟨algebraMap L K, (algebraMap L K).injective⟩
    let Z : Finset K := insert x (Finset.univ.map e)
    have hxZ : x ∉ Finset.univ.map e := by
      intro hm
      rw [Finset.mem_map] at hm
      obtain ⟨a, -, ha⟩ := hm
      exact hne ⟨a, ha⟩
    have hcard : Z.card = Fintype.card L + 1 := by
      rw [Finset.card_insert_of_notMem hxZ, Finset.card_map, Finset.card_univ]
    have h1 : 1 < Fintype.card L := Fintype.one_lt_card
    have hne0 : (X ^ Fintype.card L - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K h1
    have hsub : Z.val ⊆ (X ^ Fintype.card L - X : K[X]).roots := by
      intro z hz
      rw [mem_roots hne0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      have hz' : z ∈ Z := hz
      rcases Finset.mem_insert.mp hz' with rfl | hm
      · exact hx
      · rw [Finset.mem_map] at hm
        obtain ⟨a, -, rfl⟩ := hm
        change (algebraMap L K a) ^ Fintype.card L = algebraMap L K a
        rw [← map_pow, FiniteField.pow_card]
    have := Polynomial.card_le_degree_of_subset_roots hsub
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq K h1, hcard] at this
    omega
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

variable {F : Type*} [Field F] (W : WeierstrassCurve F) {K : Type*} [Field K] [DecidableEq K]
  [Algebra F K]

/-- If the fixed elements of `τ : K →ₐ[F] K` are exactly (the image of) an intermediate field `L`,
then the points of `W(K)` fixed by `τ` are exactly the image of `W(L)`. -/
theorem mapPt_eq_self_iff_of_fixed (L : Type*) [Field L] [DecidableEq L] [Algebra F L]
    [Algebra L K] [IsScalarTower F L K] (τ : K →ₐ[F] K)
    (hτ : ∀ x, τ x = x ↔ x ∈ (algebraMap L K).range) (P : (W.baseChange K).toAffine.Point) :
    mapPt W τ P = P ↔ P ∈ (Affine.Point.baseChange (W' := W.toAffine) L K).range := by
  constructor
  · rcases P with _ | ⟨x, y, h⟩
    · intro _
      exact ⟨0, rfl⟩
    · intro hP
      have hP' : τ x = x ∧ τ y = y := by
        simpa [mapPt, Affine.Point.map_some] using hP
      obtain ⟨hx, hy⟩ := hP'
      rw [hτ] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      have h' : (W.toAffine.baseChange L).Nonsingular a b :=
        (W.toAffine.baseChange_nonsingular (f := Algebra.ofId L K)
          (Algebra.ofId L K).injective a b).mp h
      exact ⟨.some a b h', rfl⟩
  · rintro ⟨Q, rfl⟩
    rcases Q with _ | ⟨a, b, h⟩
    · rfl
    · have ha : τ (algebraMap L K a) = algebraMap L K a := (hτ _).mpr ⟨a, rfl⟩
      have hb : τ (algebraMap L K b) = algebraMap L K b := (hτ _).mpr ⟨b, rfl⟩
      simp only [mapPt, Affine.Point.baseChange, Affine.Point.map_some, Algebra.ofId_apply, ha, hb]

/-- If `τ` acts on `K` as `x ↦ x ^ #L` for an intermediate finite field `L`, then the points of
`W(K)` fixed by `τ` are exactly the image of `W(L)`. -/
theorem mapPt_eq_self_iff (L : Type*) [Field L] [Fintype L] [DecidableEq L] [Algebra F L]
    [Algebra L K] [IsScalarTower F L K] (τ : K →ₐ[F] K) (hτ : ∀ x, τ x = x ^ Fintype.card L)
    (P : (W.baseChange K).toAffine.Point) :
    mapPt W τ P = P ↔ P ∈ (Affine.Point.baseChange (W' := W.toAffine) L K).range :=
  mapPt_eq_self_iff_of_fixed W L τ (fun x => by rw [hτ, pow_card_eq_self_iff]) P

end Fixed

/-! ## The subfield `𝔽_{q^m}` of an extension -/

section PowFixedField

variable {F : Type*} [Field F] [Fintype F] (K : Type*) [Field K] [Algebra F K]

lemma frobeniusAlgHom_pow_apply (m : ℕ) (x : K) :
    (FiniteField.frobeniusAlgHom F K ^ m) x = x ^ (Fintype.card F ^ m) := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

/-- The intermediate field `{x ∈ K | x ^ (q ^ m) = x}` of an extension `K` of `F`, `q = #F`.
For `K` algebraically closed and `m ≠ 0` it is the copy of `𝔽_{q^m}` in `K`
(`card_powFixedField`). -/
def powFixedField (m : ℕ) : IntermediateField F K :=
  Subalgebra.toIntermediateField
    (AlgHom.equalizer (FiniteField.frobeniusAlgHom F K ^ m) (AlgHom.id F K))
    (fun x hx => by
      rw [AlgHom.mem_equalizer] at hx ⊢
      rw [map_inv₀, hx, AlgHom.id_apply, AlgHom.id_apply])

lemma mem_powFixedField (m : ℕ) (x : K) :
    x ∈ powFixedField (F := F) K m ↔ x ^ (Fintype.card F ^ m) = x := by
  change x ∈ AlgHom.equalizer (FiniteField.frobeniusAlgHom F K ^ m) (AlgHom.id F K) ↔ _
  rw [AlgHom.mem_equalizer, AlgHom.id_apply, frobeniusAlgHom_pow_apply]

lemma mem_range_algebraMap_powFixedField (m : ℕ) (x : K) :
    x ∈ (algebraMap (powFixedField (F := F) K m) K).range ↔ x ^ (Fintype.card F ^ m) = x := by
  rw [← mem_powFixedField]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- In an algebraically closed extension, `{x | x ^ (q ^ m) = x}` has exactly `q ^ m` elements
(`m ≠ 0`): it is `𝔽_{q^m}`. -/
theorem card_powFixedField [IsAlgClosed K] {m : ℕ} (hm : m ≠ 0) :
    Nat.card (powFixedField (F := F) K m) = Fintype.card F ^ m := by
  classical
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hQ1 : 1 < Fintype.card F ^ m := Nat.one_lt_pow hm hq1
  have hP0 : (X ^ (Fintype.card F ^ m) - X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hQ1
  have : CharP K (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F K).injective (ringChar F)
  have hdvd : ringChar F ∣ Fintype.card F ^ m := by
    rw [← CharP.cast_eq_zero_iff K (ringChar F), Nat.cast_pow, ← map_natCast (algebraMap F K),
      FiniteField.cast_card_eq_zero, map_zero, zero_pow hm]
  have hsep : (X ^ (Fintype.card F ^ m) - X : K[X]).Separable :=
    galois_poly_separable (ringChar F) _ hdvd
  have hnodup := Polynomial.nodup_roots hsep
  have hroots : (X ^ (Fintype.card F ^ m) - X : K[X]).roots.card = Fintype.card F ^ m := by
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits _),
      FiniteField.X_pow_card_sub_X_natDegree_eq K hQ1]
  have e : (powFixedField (F := F) K m) ≃
      {x : K // x ∈ (X ^ (Fintype.card F ^ m) - X : K[X]).roots.toFinset} :=
    Equiv.subtypeEquivRight fun x => by
      rw [mem_powFixedField, Multiset.mem_toFinset, mem_roots hP0, IsRoot, eval_sub, eval_pow,
        eval_X, sub_eq_zero]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup hnodup, hroots]

theorem finite_powFixedField [IsAlgClosed K] {m : ℕ} (hm : m ≠ 0) :
    Finite (powFixedField (F := F) K m) :=
  Nat.finite_of_card_ne_zero (by rw [card_powFixedField K hm]; positivity)

end PowFixedField

/-! ## The Frobenius on points -/

section Frobenius

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) (K : Type*) [Field K]
  [DecidableEq K] [Algebra F K]

/-- The `q`-power Frobenius `(x, y) ↦ (x ^ q, y ^ q)` on `W(K)`, `q = #F`, an additive
endomorphism, for any extension `K / F`. -/
noncomputable def frob : (W.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point :=
  mapPt W (FiniteField.frobeniusAlgHom F K)

lemma frob_zero : frob W K 0 = 0 := rfl

lemma frob_some {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange K).toAffine.Nonsingular (x ^ Fintype.card F) (y ^ Fintype.card F),
      frob W K (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

lemma frob_injective : Function.Injective (frob W K) :=
  mapPt_injective W _

/-- The `m`-th iterate of the Frobenius is induced by `x ↦ x ^ (q ^ m)`. -/
lemma frob_iterate (m : ℕ) (P : (W.baseChange K).toAffine.Point) :
    (frob W K)^[m] P = mapPt W (FiniteField.frobeniusAlgHom F K ^ m) P := by
  induction m with
  | zero => exact (mapPt_id W P).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, frob, mapPt_comp, pow_succ']
    rfl

/-- The points fixed by the Frobenius are exactly the image of `W(F)`. -/
theorem frob_eq_self_iff [DecidableEq F] (P : (W.baseChange K).toAffine.Point) :
    frob W K P = P ↔ P ∈ (baseChangePt W K).range :=
  mapPt_eq_self_iff W F (FiniteField.frobeniusAlgHom F K) (fun _ => rfl) P

/-- The points fixed by the `m`-th iterate of the Frobenius are exactly the image of `W(L)` for
any intermediate field `F ⊆ L ⊆ K` with `#L = q ^ m`. -/
theorem frob_iterate_eq_self_iff (m : ℕ) (L : Type*) [Field L] [Fintype L] [DecidableEq L]
    [Algebra F L] [Algebra L K] [IsScalarTower F L K] (hL : Fintype.card L = Fintype.card F ^ m)
    (P : (W.baseChange K).toAffine.Point) :
    (frob W K)^[m] P = P ↔ P ∈ (Affine.Point.baseChange (W' := W.toAffine) L K).range := by
  rw [frob_iterate]
  exact mapPt_eq_self_iff W L _ (fun x => by rw [frobeniusAlgHom_pow_apply, hL]) P

/-- The points fixed by the `m`-th iterate of the Frobenius are exactly the image of
`W(𝔽_{q^m})`, where `𝔽_{q^m} = powFixedField K m ⊆ K` (no hypothesis on `K`). -/
theorem frob_iterate_eq_self_iff_powFixedField (m : ℕ) (P : (W.baseChange K).toAffine.Point) :
    (frob W K)^[m] P = P ↔
      P ∈ (Affine.Point.baseChange (W' := W.toAffine) (powFixedField (F := F) K m) K).range := by
  rw [frob_iterate]
  exact mapPt_eq_self_iff_of_fixed W _ _ (fun x => by
    rw [frobeniusAlgHom_pow_apply, mem_range_algebraMap_powFixedField]) P

/-- `N(W/F)` counts the Frobenius-fixed points of `W(K)`. -/
theorem numPoints_eq_card_fixed [DecidableEq F] :
    numPoints W = Nat.card {P : (W.baseChange K).toAffine.Point // frob W K P = P} := by
  rw [numPoints]
  refine Nat.card_congr ((Equiv.ofInjective _ (baseChangePt_injective W K)).trans
    (Equiv.subtypeEquivRight fun P => ?_))
  rw [frob_eq_self_iff, AddMonoidHom.mem_range, Set.mem_range]

/-- `N(W/L)` counts the points of `W(K)` fixed by the `m`-th iterate of the Frobenius,
for `F ⊆ L ⊆ K` with `#L = q ^ m`. -/
theorem numPoints_baseChange_eq_card_fixed (m : ℕ) (L : Type*) [Field L] [Fintype L]
    [DecidableEq L] [Algebra F L] [Algebra L K] [IsScalarTower F L K]
    (hL : Fintype.card L = Fintype.card F ^ m) :
    numPoints (W.baseChange L) =
      Nat.card {P : (W.baseChange K).toAffine.Point // (frob W K)^[m] P = P} := by
  rw [numPoints]
  refine Nat.card_congr ((Equiv.ofInjective _
    (Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId L K))).trans
    (Equiv.subtypeEquivRight fun P => ?_))
  rw [frob_iterate_eq_self_iff W K m L hL, AddMonoidHom.mem_range, Set.mem_range]

/-- `N(W/𝔽_{q^m})` counts the points of `W(K)` fixed by the `m`-th iterate of the Frobenius,
with `𝔽_{q^m} = powFixedField K m` (of cardinality `q ^ m` when `K` is algebraically closed and
`m ≠ 0`, see `card_powFixedField`). -/
theorem numPoints_powFixedField_eq_card_fixed (m : ℕ) :
    numPoints (W.baseChange (powFixedField (F := F) K m)) =
      Nat.card {P : (W.baseChange K).toAffine.Point // (frob W K)^[m] P = P} := by
  rw [numPoints]
  refine Nat.card_congr ((Equiv.ofInjective _
    (Affine.Point.map_injective (W' := W.toAffine)
      (Algebra.ofId (powFixedField (F := F) K m) K))).trans
    (Equiv.subtypeEquivRight fun P => ?_))
  rw [frob_iterate_eq_self_iff_powFixedField, AddMonoidHom.mem_range, Set.mem_range]

/-- For an algebraic extension `K / F` (e.g. an algebraic closure) the Frobenius is an additive
automorphism of `W(K)`. -/
noncomputable def frobAut [Algebra.IsAlgebraic F K] :
    (W.baseChange K).toAffine.Point ≃+ (W.baseChange K).toAffine.Point :=
  mapPtEquiv W (FiniteField.frobeniusAlgEquivOfAlgebraic F K)

lemma frobAut_apply [Algebra.IsAlgebraic F K] (P : (W.baseChange K).toAffine.Point) :
    frobAut W K P = frob W K P := rfl

lemma coe_frobAut [Algebra.IsAlgebraic F K] : ⇑(frobAut W K) = ⇑(frob W K) :=
  funext fun P => frobAut_apply W K P

lemma frob_bijective [Algebra.IsAlgebraic F K] : Function.Bijective (frob W K) := by
  rw [← coe_frobAut]
  exact (frobAut W K).bijective

/-- The Frobenius automorphism fixes exactly the image of `W(F)`. -/
theorem frobAut_eq_self_iff [DecidableEq F] [Algebra.IsAlgebraic F K]
    (P : (W.baseChange K).toAffine.Point) :
    frobAut W K P = P ↔ P ∈ (baseChangePt W K).range := by
  rw [frobAut_apply]
  exact frob_eq_self_iff W K P

/-- The `m`-th iterate of the Frobenius automorphism fixes exactly the image of `W(L)`,
`F ⊆ L ⊆ K`, `#L = q ^ m`. -/
theorem frobAut_iterate_eq_self_iff [Algebra.IsAlgebraic F K] (m : ℕ) (L : Type*) [Field L]
    [Fintype L] [DecidableEq L] [Algebra F L] [Algebra L K] [IsScalarTower F L K]
    (hL : Fintype.card L = Fintype.card F ^ m) (P : (W.baseChange K).toAffine.Point) :
    (⇑(frobAut W K))^[m] P = P ↔ P ∈ (Affine.Point.baseChange (W' := W.toAffine) L K).range := by
  rw [coe_frobAut]
  exact frob_iterate_eq_self_iff W K m L hL P

end Frobenius

/-! ## Invariance of the point count under a change of variables -/

section VariableChange

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The coordinate map of a change of variables:
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`, as a bijection of `F × F`. -/
noncomputable def vcCoord (C : VariableChange F) : F × F ≃ F × F where
  toFun p := ((C.u : F) ^ 2 * p.1 + C.r, (C.u : F) ^ 3 * p.2 + (C.u : F) ^ 2 * C.s * p.1 + C.t)
  invFun q := (((C.u : F) ^ 2)⁻¹ * (q.1 - C.r),
    ((C.u : F) ^ 3)⁻¹ * (q.2 - C.s * (q.1 - C.r) - C.t))
  left_inv p := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp only <;> field_simp <;> ring
  right_inv q := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp only <;> field_simp <;> ring

/-- A point `(x, y)` lies on `C • W` iff its image under the coordinate change lies on `W`. -/
lemma equation_variableChange (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have e1 : (C.u : F) * (C • W).a₁ = W.a₁ + 2 * C.s := by
    rw [variableChange_a₁, Units.val_inv_eq_inv_val]; field_simp
  have e2 : (C.u : F) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
    rw [variableChange_a₂, Units.val_inv_eq_inv_val]; field_simp
  have e3 : (C.u : F) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
    rw [variableChange_a₃, Units.val_inv_eq_inv_val]; field_simp
  have e4 : (C.u : F) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ -
      (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t := by
    rw [variableChange_a₄, Units.val_inv_eq_inv_val]; field_simp
  have e6 : (C.u : F) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 -
      C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
    rw [variableChange_a₆, Units.val_inv_eq_inv_val]; field_simp
  rw [equation_iff', equation_iff']
  set u : F := (C.u : F)
  have key : ((u ^ 3 * y + u ^ 2 * C.s * x + C.t) ^ 2 +
      W.a₁ * (u ^ 2 * x + C.r) * (u ^ 3 * y + u ^ 2 * C.s * x + C.t) +
      W.a₃ * (u ^ 3 * y + u ^ 2 * C.s * x + C.t) -
      ((u ^ 2 * x + C.r) ^ 3 + W.a₂ * (u ^ 2 * x + C.r) ^ 2 + W.a₄ * (u ^ 2 * x + C.r) + W.a₆)) =
      u ^ 6 * (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y -
        (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) := by
    linear_combination (-(u ^ 5 * x * y)) * e1 - (u ^ 3 * y) * e3 + (u ^ 4 * x ^ 2) * e2 +
      (u ^ 2 * x) * e4 + e6
  rw [key]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 6 hu)

/-- A change of variables gives a bijection of points (for elliptic curves). -/
noncomputable def variableChangePointEquiv [W.IsElliptic] (C : VariableChange F) :
    (C • W).toAffine.Point ≃ W.toAffine.Point :=
  (pointEquiv (C • W).toAffine).trans <|
    (Equiv.optionCongr <| (vcCoord C).subtypeEquiv fun p =>
      equation_variableChange W C p.1 p.2).trans (pointEquiv W.toAffine).symm

/-- `N` is invariant under a change of variables. -/
theorem numPoints_variableChange [W.IsElliptic] (C : VariableChange F) :
    numPoints (C • W) = numPoints W :=
  Nat.card_congr (variableChangePointEquiv W C)

/-- `a` is invariant under a change of variables. -/
theorem trace_variableChange [W.IsElliptic] (C : VariableChange F) :
    trace (C • W) = trace W := by
  rw [trace, trace, numPoints_variableChange]

end VariableChange

/-! ## Sanity checks -/

section Sanity

/-- `y² = x³ + 1` over `𝔽₅`. -/
def W51 : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 0, 1⟩

/-- `y² = x³ + x + 1` over `𝔽₅`. -/
def W52 : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩

theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] fact_prime_five

theorem isElliptic_W51 : W51.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide

theorem isElliptic_W52 : W52.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide

attribute [local instance] isElliptic_W51 isElliptic_W52

theorem numPoints_W51 : numPoints W51 = 6 := by
  rw [numPoints_eq_card_filter]
  decide

theorem trace_W51 : trace W51 = 0 := by
  rw [trace_eq, numPoints_W51, ZMod.card]
  norm_num

theorem numPoints_W52 : numPoints W52 = 9 := by
  rw [numPoints_eq_card_filter]
  decide

theorem trace_W52 : trace W52 = -3 := by
  rw [trace_eq, numPoints_W52, ZMod.card]
  norm_num

/-- Sanity check of `card_powFixedField`: `𝔽₂₅ ⊆ 𝔽̄₅` has 25 elements. -/
example : Nat.card (powFixedField (F := ZMod 5) (AlgebraicClosure (ZMod 5)) 2) = 25 := by
  rw [card_powFixedField _ two_ne_zero, ZMod.card]
  norm_num

open Classical in
/-- Sanity check of `frob_eq_self_iff`: the Frobenius on `W51(𝔽̄₅)` fixes exactly 6 points. -/
example : Nat.card {P : (W51.baseChange (AlgebraicClosure (ZMod 5))).toAffine.Point //
    frob W51 (AlgebraicClosure (ZMod 5)) P = P} = 6 := by
  rw [← numPoints_eq_card_fixed, numPoints_W51]

end Sanity

end RPLib.EllFq


