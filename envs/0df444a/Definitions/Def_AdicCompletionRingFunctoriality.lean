-- Prove2me | Definitions.Def_AdicCompletionRingFunctoriality
-- name    : AdicCompletionRingFunctoriality
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/070f183d-b02d-5c37-bc7e-cf3dcce40a00
-- title:
--   Functoriality of adic completions for algebra maps
-- statement:
--   Throughout, $k$ is a commutative ring and $R$, $S$, $T$ are commutative $k$-algebras. The first group of declarations constructs the levelwise maps. Given ideals $I \subseteq R$, $J \subseteq S$ and a $k$-algebra map $f : R \to S$ with $f(I)S \subseteq J$ (written `I.map f ≤ J`), `pow_le_comap_pow` records that $I^n \subseteq f^{-1}(J^n)$ for every $n$, and `levelMapₐ` is the resulting $k$-algebra map $R/I^n \to S/J^n$ obtained from `Ideal.quotientMapₐ`; `levelMapₐ_mk` says it sends the class of $x$ to the class of $f(x)$. These maps commute with the transition maps `Ideal.Quotient.factorPow` between successive quotients (`factorPow_levelMapₐ`), are the identity for $f = \mathrm{id}$ and compose contravariantly along $g \circ f$ (`levelMapₐ_id`, `levelMapₐ_comp`), and are surjective when $f$ is (`levelMapₐ_surjective_of_surjective`).
--
--   The second group passes to the completions. `mapₐAux` is the composite of evaluation `evalₐ I n` at level $n$ with `levelMapₐ`, a $k$-algebra map $\widehat{R}_I \to S/J^n$; `factorₐ_comp_mapₐAux` is its compatibility with the transition maps, and `mapₐ` is the induced $k$-algebra map $\widehat{R}_I \to \widehat{S}_J$ of adic completions obtained from the universal property `liftAlgHom`. It is characterised by `evalₐ_mapₐ`, namely $\mathrm{ev}_n(\mathrm{map}(x)) = \mathrm{levelMap}_n(\mathrm{ev}_n(x))$, and sends $\mathrm{of}(x)$ to $\mathrm{of}(f(x))$ (`mapₐ_of`). Further lemmas give invariance under equality of the maps (`mapₐ_congr`), the identity law, the composition law in the forms `mapₐ_comp` and `mapₐ_comp_apply`, and the auxiliary fact `map_comp_le` that the hypotheses on $f$ and $g$ imply the one for $g \circ f$.
--
--   The last group produces isomorphisms. `mapAlgEquiv` turns a $k$-algebra isomorphism $e : R \simeq S$ with $e(I)S \subseteq J$ and $e^{-1}(J)R \subseteq I$ into an isomorphism $\widehat{R}_I \simeq \widehat{S}_J$, with `mapₐ` of $e$ and of $e^{-1}$ as the two directions. Alternatively, from a single $f$ whose levelwise maps are all bijective, `levelEquiv` packages each `levelMapₐ` as a ring isomorphism $R/I^n \simeq S/J^n$, `factorPow_levelEquiv` is its compatibility with the transition maps, and `mapAlgEquivOfBijective` is the resulting $k$-algebra isomorphism of completions, built from `ofLevelwiseEquiv`. Its underlying function agrees with `mapₐ` (`mapAlgEquivOfBijective_apply`, `coe_mapAlgEquivOfBijective`), whence `mapₐ_bijective`; the remaining lemmas compute it and its inverse on elements of the form $\mathrm{of}(x)$ and levelwise.
--
--   **Relation to Mathlib.** Mathlib supplies the adic completion $\widehat{R}_I$ with its evaluation maps `evalₐ`, the canonical map `of` and the universal property `liftAlgHom`, together with `Ideal.quotientMapₐ` on quotients; the functoriality of the completion in the pair (ring, ideal), i.e. the induced algebra maps and isomorphisms between completions of different rings along different ideals, is added here.
--
--   **Where it is used.** The construction is used together with the identification of the adic completion of a localised polynomial ring with a power series ring, which is where comparisons of completions along algebra maps are needed in the commutative algebra underlying the deformation-ring arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AdicCompletionRingFunctoriality.lean

import Definitions.Def_PolynomialCompletion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]
variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra k R] [Algebra k S] [Algebra k T]

section LevelMap

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

theorem pow_le_comap_pow (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

def levelMapₐ (h : I.map f ≤ J) (n : ℕ) : R ⧸ I ^ n →ₐ[k] S ⧸ J ^ n :=
  Ideal.quotientMapₐ (J ^ n) f (pow_le_comap_pow I J f h n)

@[simp]
theorem levelMapₐ_mk (h : I.map f ≤ J) (n : ℕ) (x : R) :
    levelMapₐ I J f h n (Ideal.Quotient.mk (I ^ n) x) = Ideal.Quotient.mk (J ^ n) (f x) :=
  rfl

theorem factorPow_levelMapₐ (h : I.map f ≤ J) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (levelMapₐ I J f h n x)
      = levelMapₐ I J f h m (Ideal.Quotient.factorPow I hmn x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem levelMapₐ_id (hI : I.map (AlgHom.id k R) ≤ I) (n : ℕ) (x : R ⧸ I ^ n) :
    levelMapₐ I I (AlgHom.id k R) hI n x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem levelMapₐ_comp (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K)
    (hgf : I.map (g.comp f) ≤ K) (n : ℕ) (x : R ⧸ I ^ n) :
    levelMapₐ I K (g.comp f) hgf n x = levelMapₐ J K g hg n (levelMapₐ I J f h n x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem levelMapₐ_surjective_of_surjective (h : I.map f ≤ J) (hf : Function.Surjective f)
    (n : ℕ) :
    Function.Surjective (levelMapₐ I J f h n) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

end LevelMap

section Map

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

noncomputable def mapₐAux (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I R →ₐ[k] S ⧸ J ^ n :=
  (levelMapₐ I J f h n).comp ((evalₐ I n).restrictScalars k)

theorem mapₐAux_apply (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    mapₐAux I J f h n x = levelMapₐ I J f h n (evalₐ I n x) :=
  rfl

theorem factorₐ_comp_mapₐAux (h : I.map f ≤ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hle)).comp (mapₐAux I J f h n)
      = mapₐAux I J f h m := by
  ext x
  show Ideal.Quotient.factorPow J hle (levelMapₐ I J f h n (evalₐ I n x))
    = levelMapₐ I J f h m (evalₐ I m x)
  rw [factorPow_levelMapₐ, factorPow_evalₐ]

noncomputable def mapₐ (h : I.map f ≤ J) : AdicCompletion I R →ₐ[k] AdicCompletion J S :=
  liftAlgHom J (mapₐAux I J f h) (factorₐ_comp_mapₐAux I J f h)

@[simp]
theorem evalₐ_mapₐ (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (mapₐ I J f h x) = levelMapₐ I J f h n (evalₐ I n x) :=
  evalₐ_liftAlgHom J (mapₐAux I J f h) (factorₐ_comp_mapₐAux I J f h) n x

@[simp]
theorem mapₐ_of (h : I.map f ≤ J) (x : R) : mapₐ I J f h (of I R x) = of J S (f x) :=
  ext_evalₐ fun n => by rw [evalₐ_mapₐ, evalₐ_of, evalₐ_of, levelMapₐ_mk]

theorem mapₐ_congr {f g : R →ₐ[k] S} (hfg : f = g) (hf : I.map f ≤ J) (hg : I.map g ≤ J) :
    mapₐ I J f hf = mapₐ I J g hg := by
  subst hfg
  rfl

theorem mapₐ_id (hI : I.map (AlgHom.id k R) ≤ I) :
    mapₐ I I (AlgHom.id k R) hI = AlgHom.id k (AdicCompletion I R) :=
  AlgHom.ext fun x => ext_evalₐ fun n => by
    rw [evalₐ_mapₐ, levelMapₐ_id]
    rfl

theorem mapₐ_comp (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K)
    (hgf : I.map (g.comp f) ≤ K) :
    mapₐ I K (g.comp f) hgf = (mapₐ J K g hg).comp (mapₐ I J f h) :=
  AlgHom.ext fun x => ext_evalₐ fun n => by
    simp only [evalₐ_mapₐ, AlgHom.comp_apply]
    rw [levelMapₐ_comp I J f h K g hg hgf]

theorem map_comp_le (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K) :
    I.map (g.comp f) ≤ K := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact Ideal.mem_comap.mpr (hg (Ideal.mem_map_of_mem g (h (Ideal.mem_map_of_mem f hx))))

theorem mapₐ_comp_apply (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K)
    (x : AdicCompletion I R) :
    mapₐ J K g hg (mapₐ I J f h x) = mapₐ I K (g.comp f) (map_comp_le I J f h K g hg) x := by
  rw [mapₐ_comp I J f h K g hg]
  rfl

end Map

section Equiv

variable (I : Ideal R) (J : Ideal S)

noncomputable def mapAlgEquiv (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) :
    AdicCompletion I R ≃ₐ[k] AdicCompletion J S :=
  AlgEquiv.ofAlgHom (mapₐ I J (e : R →ₐ[k] S) he) (mapₐ J I (e.symm : S →ₐ[k] R) he')
    (AlgHom.ext fun y => ext_evalₐ fun n => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ J n y)
      rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_mapₐ, evalₐ_mapₐ, ← hz]
      show Ideal.Quotient.mk (J ^ n) (e (e.symm z)) = Ideal.Quotient.mk (J ^ n) z
      rw [AlgEquiv.apply_symm_apply])
    (AlgHom.ext fun x => ext_evalₐ fun n => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_mapₐ, evalₐ_mapₐ, ← hz]
      show Ideal.Quotient.mk (I ^ n) (e.symm (e z)) = Ideal.Quotient.mk (I ^ n) z
      rw [AlgEquiv.symm_apply_apply])

@[simp]
theorem mapAlgEquiv_apply (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) (x : AdicCompletion I R) :
    mapAlgEquiv I J e he he' x = mapₐ I J (e : R →ₐ[k] S) he x :=
  rfl

@[simp]
theorem mapAlgEquiv_symm_apply (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) (y : AdicCompletion J S) :
    (mapAlgEquiv I J e he he').symm y = mapₐ J I (e.symm : S →ₐ[k] R) he' y :=
  rfl

variable (f : R →ₐ[k] S)

noncomputable def levelEquiv (h : I.map f ≤ J) (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n))
    (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ J ^ n :=
  RingEquiv.ofBijective (levelMapₐ I J f h n) (hb n)

theorem levelEquiv_apply (h : I.map f ≤ J) (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n))
    (n : ℕ) (x : R ⧸ I ^ n) :
    levelEquiv I J f h hb n x = levelMapₐ I J f h n x :=
  rfl

theorem factorPow_levelEquiv (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (levelEquiv I J f h hb n x)
      = levelEquiv I J f h hb m (Ideal.Quotient.factorPow I hmn x) :=
  factorPow_levelMapₐ I J f h hmn x

noncomputable def mapAlgEquivOfBijective (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) :
    AdicCompletion I R ≃ₐ[k] AdicCompletion J S :=
  AlgEquiv.ofRingEquiv
    (f := ofLevelwiseEquiv I J (levelEquiv I J f h hb) (factorPow_levelEquiv I J f h hb))
    (fun c => by
      rw [algebraMap_apply, algebraMap_apply]
      refine ofLevelwiseEquiv_of I J _ _ _ _ fun n => ?_
      rw [levelEquiv_apply, levelMapₐ_mk, AlgHom.commutes])

@[simp]
theorem mapAlgEquivOfBijective_apply (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (x : AdicCompletion I R) :
    mapAlgEquivOfBijective I J f h hb x = mapₐ I J f h x :=
  ext_evalₐ fun n => by
    show evalₐ J n (ofLevelwiseEquiv I J (levelEquiv I J f h hb)
      (factorPow_levelEquiv I J f h hb) x) = _
    rw [evalₐ_ofLevelwiseEquiv, evalₐ_mapₐ, levelEquiv_apply]

theorem coe_mapAlgEquivOfBijective (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) :
    (mapAlgEquivOfBijective I J f h hb : AdicCompletion I R →ₐ[k] AdicCompletion J S)
      = mapₐ I J f h :=
  AlgHom.ext (mapAlgEquivOfBijective_apply I J f h hb)

theorem mapₐ_bijective (h : I.map f ≤ J) (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) :
    Function.Bijective (mapₐ I J f h) := by
  have hB := (mapAlgEquivOfBijective I J f h hb).bijective
  rwa [show ⇑(mapAlgEquivOfBijective I J f h hb) = ⇑(mapₐ I J f h) from
    funext (mapAlgEquivOfBijective_apply I J f h hb)] at hB

theorem mapAlgEquivOfBijective_of (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (x : R) :
    mapAlgEquivOfBijective I J f h hb (of I R x) = of J S (f x) := by
  rw [mapAlgEquivOfBijective_apply, mapₐ_of]

theorem levelMapₐ_evalₐ_mapAlgEquivOfBijective_symm (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (n : ℕ) (y : AdicCompletion J S) :
    levelMapₐ I J f h n (evalₐ I n ((mapAlgEquivOfBijective I J f h hb).symm y)) = evalₐ J n y := by
  conv_rhs => rw [← (mapAlgEquivOfBijective I J f h hb).apply_symm_apply y]
  rw [mapAlgEquivOfBijective_apply, evalₐ_mapₐ]

theorem mapAlgEquivOfBijective_symm_of (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (x : R) :
    (mapAlgEquivOfBijective I J f h hb).symm (of J S (f x)) = of I R x := by
  rw [AlgEquiv.symm_apply_eq, mapAlgEquivOfBijective_of]

end Equiv

end AdicCompletion

#print axioms AdicCompletion.mapₐ
#print axioms AdicCompletion.mapₐ_of
#print axioms AdicCompletion.mapₐ_id
#print axioms AdicCompletion.mapₐ_comp
#print axioms AdicCompletion.mapAlgEquiv
#print axioms AdicCompletion.mapAlgEquivOfBijective
#print axioms AdicCompletion.mapAlgEquivOfBijective_apply
#print axioms AdicCompletion.mapₐ_bijective


