-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_100
-- name    : RPLib_FX_EtPBC_100
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:55:13.130171+00:00
-- url     : https://prove2.me/theorems/2278bb2b-b521-5a0e-b25b-15b9b02ff853
-- title:
--   Proper base change for the projective line, library file 100
-- statement:
--   File 100 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_Emb`: S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`
--   * `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
--   * `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_089
import Definitions.Def_RPLib_FX_EtPBC_096

/-!
# Proper base change for the projective line, library file 100

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_Emb`: S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`
* `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
* `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_Emb =====
section

/-!
# S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`

* `bcSurj_zero_of_hom`, `hom_of_bcSurj_zero`: `BCSurj 0` as a statement about morphisms `Λ_{P_s} ⟶ ι^* H`;
* **`bcSurj_of_mono`**: `BCSurj 0` passes to subobjects (`g` universally closed: `bcInj_zero` on the cokernel);
* **`bcSurj_biprod`**: `BCSurj 0` for `H₁` and `H₂` gives it for `H₁ ⊞ H₂`;
* `EmbC F`: `F` embeds into a sheaf with `BCSurj 0`; **`bcSurj_of_embC`**, **`embC_of_mono`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `BCSurj 0` from lifts of morphisms. -/
theorem bcSurj_zero_of_hom {H : EtSh Λ P}
    (h : ∀ b : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj H,
      ∃ (j : Nbhd s) (φ : (nbhdSys Λ g s).obj j ⟶ H), bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map φ = b) :
    BCSurj Λ g s 0 H := by
  intro β
  obtain ⟨j, φ, hφ⟩ := h (Ext.addEquiv₀ β)
  refine ⟨j, Ext.addEquiv₀.symm φ, ?_⟩
  exact (bc_zero_eq Λ g s j H _).trans
    ((congrArg (fun φ' => Ext.mk₀ (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map φ')) (AddEquiv.apply_symm_apply _ _)).trans
      ((congrArg Ext.mk₀ hφ).trans (Ext.mk₀_addEquiv₀_apply β)))

/-- Lifts of morphisms from `BCSurj 0`. -/
theorem hom_of_bcSurj_zero {H : EtSh Λ P} (hH : BCSurj Λ g s 0 H)
    (b : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj H) :
    ∃ (j : Nbhd s) (φ : (nbhdSys Λ g s).obj j ⟶ H), bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map φ = b := by
  obtain ⟨j, α, hα⟩ := hH (Ext.mk₀ b)
  exact ⟨j, Ext.addEquiv₀ α, (Ext.mk₀_bijective _ _).1 ((bc_zero_eq Λ g s j H α).symm.trans hα)⟩

/-- **`BCSurj 0` for a binary biproduct.** -/
theorem bcSurj_biprod {H₁ H₂ : EtSh Λ P} (h₁ : BCSurj Λ g s 0 H₁) (h₂ : BCSurj Λ g s 0 H₂) :
    BCSurj Λ g s 0 (H₁ ⊞ H₂) := by
  apply bcSurj_zero_of_hom
  intro b
  obtain ⟨j₁, φ₁, hφ₁⟩ := hom_of_bcSurj_zero g s h₁ (b ≫ (pull (fibι g s) Λ).map biprod.fst)
  obtain ⟨j₂, φ₂, hφ₂⟩ := hom_of_bcSurj_zero g s h₂ (b ≫ (pull (fibι g s) Λ).map biprod.snd)
  refine ⟨IsCofiltered.min j₁ j₂, biprod.lift ((nbhdSys Λ g s).map (IsCofiltered.minToLeft j₁ j₂) ≫ φ₁)
    ((nbhdSys Λ g s).map (IsCofiltered.minToRight j₁ j₂) ≫ φ₂), ?_⟩
  have e1 : bcUnit Λ g s (IsCofiltered.min j₁ j₂) ≫ (pull (fibι g s) Λ).map
      ((nbhdSys Λ g s).map (IsCofiltered.minToLeft j₁ j₂) ≫ φ₁) = b ≫ (pull (fibι g s) Λ).map biprod.fst := by
    rw [Functor.map_comp, ← Category.assoc, bcUnit_comp Λ g s, hφ₁]
  have e2 : bcUnit Λ g s (IsCofiltered.min j₁ j₂) ≫ (pull (fibι g s) Λ).map
      ((nbhdSys Λ g s).map (IsCofiltered.minToRight j₁ j₂) ≫ φ₂) = b ≫ (pull (fibι g s) Λ).map biprod.snd := by
    rw [Functor.map_comp, ← Category.assoc, bcUnit_comp Λ g s, hφ₂]
  have hb : b = (b ≫ (pull (fibι g s) Λ).map biprod.fst) ≫ (pull (fibι g s) Λ).map biprod.inl +
      (b ≫ (pull (fibι g s) Λ).map biprod.snd) ≫ (pull (fibι g s) Λ).map biprod.inr := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_add, biprod.total, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hb, ← e1, ← e2, biprod.lift_eq, Functor.map_add, Preadditive.comp_add]
  simp only [Functor.map_comp, Category.assoc]

/-- **Embeddings into a biproduct of embeddable sheaves.** -/
theorem embC_of_mono {F H₁ H₂ : EtSh Λ P} (m : F ⟶ H₁ ⊞ H₂) [Mono m] (h₁ : EmbC g s H₁) (h₂ : EmbC g s H₂) :
    EmbC g s F := by
  obtain ⟨H₁', m₁, hm₁, hH₁⟩ := h₁
  obtain ⟨H₂', m₂, hm₂, hH₂⟩ := h₂
  have : Mono (biprod.map m₁ m₂) := inferInstance
  exact ⟨H₁' ⊞ H₂', m ≫ biprod.map m₁ m₂, mono_comp _ _, bcSurj_biprod g s hH₁ hH₂⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NInd =====
section

/-!
# S4-EtPBC-A, M4(C,D,F): noetherian induction on supports

* `FGT Λ F`: `F` is a quotient of a finite sum `∐ Λ[W j]` with every `(W j).left` affine;
* `fgt_image`, `fgt_quotCut`; `mono_lift_of_stalk` (a stalkwise criterion for `biprod.lift a b` to be mono);
  `bcSurj_of_isZero`;
* `GenStep Λ g s`: the generic step: an `FGT` sheaf `F` with stalks zero off a nonempty closed `Z` maps to a sheaf
  with `BCSurj 0`, injectively on stalks over `V ∩ Z ≠ ∅` for some open `V`;
* **`embC_of_fgt`**: under `GenStep` (and `P` noetherian) every `FGT` sheaf embeds into a sheaf with `BCSurj 0`;
* **`bcSurj_zero_all`**: under `GenStep`, `BCSurj 0` holds for every sheaf (`P_s` compact, `g` universally closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `BCSurj 0` for a zero sheaf. -/
theorem bcSurj_of_isZero {H : EtSh Λ P} (hH : IsZero H) : BCSurj Λ g s 0 H := by
  apply bcSurj_zero_of_hom
  intro b
  obtain ⟨j⟩ : Nonempty (Nbhd s) := IsCofiltered.nonempty
  exact ⟨j, 0, ((pull (fibι g s) Λ).map_isZero hH).eq_of_tgt _ _⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapD =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class

* **`resLE_kapS_sum`**: the global class `Σ_Q kapS Q (χ Q)` restricts to `κ(χ Q)` on the piece `Q`;
* **`resLE_kapS_kumD_eq`**: for etale `f : X₁ ⟶ X`, `g : X₁ ⟶ Y` of affine schemes whose rings are finite products of
  Dedekind domains, `resLE f (kapS p (kumD α)) = resLE g c_Y` when `c_Y` is the Kummer class of a unit `H` of `Γ(Y)`
  (piecewise), `α ^ d = u`, the roots of unity match, and on every piece `p₁` of `X₁`: over `p`, `u = H · v ^ d`;
  over another piece of `X`, `H` is a `d`-th power.
  Proof: `h1_eq_zero_of_pieces` on `X₁`, `piHom_comp_eq` for `f` and `g`, `resLE_kapS_self/ne`, `resLE_kumD_eq`
  (O2KapN) and `resLE_kumD_eq_zero` (O2KapF).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section KapSum

end KapSum

section KapB

variable {A K A' K' A'' K'' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDedekindDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  [CommRing A''] [IsDomain A''] [Field K''] [Algebra A'' K''] [IsFractionRing A'' K'']
  [IsIntegrallyClosed A] [IsNoetherianRing A] [IsIntegrallyClosed A''] [IsNoetherianRing A'']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)]
  (φ'' : CommRingCat.of A'' ⟶ CommRingCat.of A') [Etale (Spec.map φ'')]
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {ζ'' : maxUnram A'' K''} (hζ'' : IsPrimitiveRoot ζ'' N)
  (hζΓ'' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A'' K'')), σ ζ'' = ζ'') {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d)
  {β : (maxUnram A'' K'')ˣ} (hβ : β ∈ rad (⊤ : Subgroup (Pi1 A'' K'')) d) {g : Λ} (hg : d • g = 0)

/-- **Ring form of the on-piece comparison** (roots of unity from elements `s`, `s''`; radicand `H''` a unit). -/
theorem resLE_kumD_eq_ring (hinj : Function.Injective φ.hom) (hinj'' : Function.Injective φ''.hom) {s : A} {s'' : A''}
    (hs : φ.hom s = φ''.hom s'') (hz : ζ = algebraMap K (maxUnram A K) (algebraMap A K s))
    (hz'' : ζ'' = algebraMap K'' (maxUnram A'' K'') (algebraMap A'' K'' s'')) {u : K}
    (hu : (α : maxUnram A K) ^ d = algebraMap K (maxUnram A K) u) {H'' : A''} (hH : IsUnit H'')
    (hu'' : (β : maxUnram A'' K'') ^ d = algebraMap K'' (maxUnram A'' K'') (algebraMap A'' K'' H''))
    (hd : IsUnit (d : A'))
    (hv : ∀ ψ : K →+* K', (∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a)) →
      ∃ v : K', ψ u = algebraMap A' K' (φ''.hom H'') * v ^ d) :
    resLE (Spec.map φ) 1 (kappaLH A K Λ (kumD hζ hζΓ hdN hα hg)) =
      resLE (Spec.map φ'') 1 (kappaLH A'' K'' Λ (kumD hζ'' hζΓ'' hdN hβ hg)) := by
  have hiK : Function.Injective ((algebraMap A' K').comp φ.hom) := (IsFractionRing.injective A' K').comp hinj
  have hiK'' : Function.Injective ((algebraMap A' K').comp φ''.hom) := (IsFractionRing.injective A' K').comp hinj''
  have hψ : ∀ a : A, IsFractionRing.lift hiK (algebraMap A K a) = algebraMap A' K' (φ.hom a) :=
    fun a => IsFractionRing.lift_algebraMap hiK a
  have hψ'' : ∀ a : A'', IsFractionRing.lift hiK'' (algebraMap A'' K'' a) = algebraMap A' K' (φ''.hom a) :=
    fun a => IsFractionRing.lift_algebraMap hiK'' a
  obtain ⟨v, hv⟩ := hv _ hψ
  exact resLE_kumD_eq φ (map_genPt_of_injective _ hinj) φ'' (map_genPt_of_injective _ hinj'') hζ hζΓ hζ'' hζΓ''
    hdN hα hβ hg (IsFractionRing.lift hiK) hψ (IsFractionRing.lift hiK'') hψ'' hz hz''
    ((hψ s).trans ((congrArg (algebraMap A' K') hs).trans (hψ'' s'').symm)) hu hu'' hd (hH.map φ''.hom)
    (hψ'' H'').symm (hv.trans (congrArg (· * v ^ d) (hψ'' H'').symm))

end KapB

section Piece

end Piece

section GenPieces

universe u'

end GenPieces

section KapD

end KapD

end RamanujanPetersson.EtPBC.EtKum

end

end


