-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_CoefModX
-- name    : Formalism_LocalToGlobal_Columns_CoefModX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:53.238156+00:00
-- url     : https://prove2.me/theorems/d0a07774-416c-4670-ab47-c4ca1678a540
-- title:
--   Coef Mod X
-- statement:
--   Definitions and structural lemmas for Coef Mod X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefModX.lean

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.L2.DIV
open Formalism.BasicNotions
def bcLat {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {n : ℕ} (j : K →+* K')
    (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K') (Fin n → K') :=
  tauLat (fun _ : Unit => j) () M
def bcPol {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {σ : Type} (j : K →+* K')
    (T : Submodule (𝓞 K) (MvPolynomial σ K)) : Submodule (𝓞 K') (MvPolynomial σ K') :=
  Submodule.span (𝓞 K') ((fun F : MvPolynomial σ K => MvPolynomial.map j F) '' (T : Set (MvPolynomial σ K)))
def polOfVV {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (T : Submodule (𝓞 K) (VV K lam)) : Submodule (𝓞 K) (Pol K ι n) :=
  T.map ((VV K lam).subtype.restrictScalars (𝓞 K))
def BaseChangeSpace : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ F : Pol K ι n, F ∈ VV K lam ↔ MvPolynomial.map j F ∈ VV K' lam) ∧
    Submodule.span K' ((fun F : Pol K ι n => MvPolynomial.map j F) '' (VV K lam : Set (Pol K ι n))) = VV K' lam
def BaseChangeAct : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) (F : Pol K ι n),
    MvPolynomial.map j (actP lam g F) = actP lam (fun τ => Formalism.UG.bc j (g τ)) (MvPolynomial.map j F)
def BaseChangePair : Prop :=
  ∀ (K K' : Type) [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'), (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n),
      pairP lam (fun τ => (G τ).map j) (MvPolynomial.map j F) (MvPolynomial.map j F') = j (pairP lam G F F')
def BaseChangeRho : Prop :=
  ∀ (E K K' : Type) [Field E] [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (x : VV K lam) (y : VV K' lam),
    (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) →
    ((rhoV (fun τ => j.comp (emb τ)) lam γ y : VV K' lam) : Pol K' ι n) =
        MvPolynomial.map j ((rhoV emb lam γ x : VV K lam) : Pol K ι n) ∧
    ((rhoVr (fun τ => j.comp (emb τ)) lam γ y : VV K' lam) : Pol K' ι n) =
        MvPolynomial.map j ((rhoVr emb lam γ x : VV K lam) : Pol K ι n)
def BaseChangePairV : Prop :=
  ∀ (E K K' : Type) [Field E] [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'),
    (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (J : Matrix (Fin n) (Fin n) E)
      (x x' : VV K lam) (y y' : VV K' lam),
      (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) → (y' : Pol K' ι n) = MvPolynomial.map j (x' : Pol K ι n) →
      pairV (fun τ => j.comp (emb τ)) lam J y y' = j (pairV emb lam J x x') ∧
      pairVr (fun τ => j.comp (emb τ)) lam J y y' = j (pairVr emb lam J x x')
def BaseChangeTauLat : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)),
    tauLat (fun τ => j.comp (emb τ)) τ L = bcLat j (tauLat emb τ L)
def BaseChangeStd : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n), bcPol j (nabStd K lam) = nabStd K' lam ∧ bcPol j (delStd K lam) = delStd K' lam
def NabDelBaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    bcPol j (nabP lam M) = nabP lam (fun τ => bcLat j (M τ)) ∧
    bcPol j (delP lam M) = delP lam (fun τ => bcLat j (M τ))
def NabDelDescent : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ F : Pol K ι n,
      (F ∈ nabP lam M ↔ MvPolynomial.map j F ∈ nabP lam (fun τ => bcLat j (M τ))) ∧
      (F ∈ delP lam M ↔ MvPolynomial.map j F ∈ delP lam (fun τ => bcLat j (M τ)))
def BaseChangeDualFr : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsLattice K M → dualFr (bcLat j M) = bcLat j (dualFr M)
def NabDelBaseChangeAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E L →
    polOfVV lam (nabAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAt emb lam L)) ∧
    polOfVV lam (delAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAt emb lam L)) ∧
    polOfVV lam (nabAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAtr emb lam L)) ∧
    polOfVV lam (delAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAtr emb lam L))
def NabDelDescentAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E L → ∀ (x : VV K lam) (y : VV K' lam), (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) →
    (x ∈ nabAt emb lam L ↔ y ∈ nabAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAt emb lam L ↔ y ∈ delAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ nabAtr emb lam L ↔ y ∈ nabAtr (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAtr emb lam L ↔ y ∈ delAtr (fun τ => j.comp (emb τ)) lam L)
end Formalism.L2.DIV


