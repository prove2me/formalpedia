-- Prove2me | Definitions.Def_ZKSheafPCP_GluingInput
-- name    : ZKSheafPCP_GluingInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:12:14.96021+00:00
-- url     : https://prove2.me/theorems/882f865b-c1f8-4510-b110-4ed2042f5ba8
-- title:
--   Inputs and output of the gluing Construction 7.5
-- statement:
--   The inputs of Construction 7.5 are a sheaf $F[t]$ on $P[t]$, a local code domain $\sigma\in P[t]$, a set $S\subseteq P[t]$, and for each $\rho\in S$ a sheaf $F[\rho]$ on $P[\rho]$, a domain $\sigma_\rho\in P[\rho]$ and an isomorphism of upper sets and of sheaf codes $h_{t,\rho}:P[t]_{\ge\rho}\to P[\rho]_{\ge\sigma_\rho}$.
--
--   The output is the **glued sheaf** on the quotient of the disjoint union of the domains by $x\sim h_{t,\rho}(x)$. Its coded space consists of the images of the elements of the pieces and of the images $h_i(P_{i*})$ of the whole pieces. The local code at an image of an element is the image of the local code, and at the image of a whole piece it is the image of $F_i(P_i)$ (Definition 4.36, Eq. (3)).
--
--   **Formalization Note** The quotient is represented by $D_t$ together with the points of each piece outside $\sigma_\rho$. The pairwise maps $h_{\rho,\tau}$ are determined by the $h_{t,\rho}$, so they add no identification. `IsGluedOutput` is a specification of the output; its existence is Proposition 4.37.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Construction 7.5, p.32; Definitions 4.20–4.36, pp.17–19

import Mathlib
import Definitions.Def_ZKSheafPCP_TestTree

namespace ZKSheafPCP

open Classical

/-- The zero-padded pullback of a word on `D` along `e : D' → D`, on the subset `α ⊆ D'`. -/
noncomputable def pullTo {F D D' : Type} [Zero F] (e : D' → D) (α : Finset D') (c : D → F) : D' → F :=
  fun x => if x ∈ α then c (e x) else 0

/-- The inputs of Construction 7.5 (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript sha256
ac5e528f…, p.32): a sheaf `F[t]` over `P[t]`, a local code domain `σ ∈ P[t]`, a set `S ⊆ P[t]`, and for each `ρ ∈ S` a
sheaf `F[ρ]` over `P[ρ]`, a domain `σ_ρ ∈ P[ρ]`, and an isomorphism `h_{t,ρ} : P[t]⩾ρ → P[ρ]⩾σ_ρ` of upper sets and of
sheaf codes (Definitions 4.14 and 4.30).

**Formalization Note** In set-family form the isomorphism is a bijection of domains; `g ρ` is its inverse
`h_{t,ρ}⁻¹ : σ_ρ → ρ`, with arbitrary values off `σ_ρ`. `hP` says it maps `P[ρ]⩾σ_ρ` onto `P[t]⩾ρ`, and `hcode` says
it maps local codes to local codes. -/
structure GluingInput (F Dt : Type) [Field F] where
  /-- the coded space `P[t]` -/
  Pt : CodedSpace Dt
  /-- the sheaf `F[t]` -/
  Ft : LocalCodes F Dt
  /-- `F[t]` is a sheaf -/
  hFt : Ft.IsSheaf Pt
  /-- the local code domain -/
  σ : Finset Dt
  hσ : σ ∈ Pt.P
  /-- the cover -/
  S : Finset (Finset Dt)
  hS : S ⊆ Pt.P
  /-- the domain of `F[ρ]` -/
  Dr : Finset Dt → Type
  [finDr : ∀ ρ, Fintype (Dr ρ)]
  /-- the coded space `P[ρ]` -/
  Pr : ∀ ρ, CodedSpace (Dr ρ)
  /-- the sheaf `F[ρ]` -/
  Fr : ∀ ρ, LocalCodes F (Dr ρ)
  hFr : ∀ ρ ∈ S, (Fr ρ).IsSheaf (Pr ρ)
  /-- the domain `σ_ρ` -/
  σr : ∀ ρ, Finset (Dr ρ)
  hσr : ∀ ρ ∈ S, σr ρ ∈ (Pr ρ).P
  /-- the inverse of `h_{t,ρ}` on domains -/
  g : ∀ ρ, Dr ρ → Dt
  hg : ∀ ρ ∈ S, Set.BijOn (g ρ) (σr ρ : Set (Dr ρ)) (ρ : Set Dt)
  hP : ∀ ρ ∈ S, ∀ α ⊆ σr ρ, α ∈ (Pr ρ).P ↔ α.image (g ρ) ∈ Pt.P
  hcode : ∀ ρ ∈ S, ∀ α ∈ (Pr ρ).P, α ⊆ σr ρ →
    pullTo (g ρ) α '' (Ft.code (α.image (g ρ)) : Set (Dt → F)) = ((Fr ρ).code α : Set (Dr ρ → F))

attribute [instance] GluingInput.finDr

namespace GluingInput

variable {F Dt : Type} [Field F] (I : GluingInput F Dt)

/-- The domain of the glued sheaf (Definitions 4.22 and 4.36, pp.17 and 19): the quotient of the disjoint union of
the domains by `x ∼ h_{t,ρ}(x)`, with `Dt` as the representatives of the glued points. It is `Dt` together with the
points of each `Dr ρ` outside `σ_ρ`.

**Formalization Note** The pairwise maps `h_{ρ,τ}` of Construction 7.5 are determined by `h_{t,ρ}`, so they add no
identification beyond this quotient. -/
abbrev GluedDom : Type :=
  Dt ⊕ Σ ρ : {ρ // ρ ∈ I.S}, {x : I.Dr ρ.1 // x ∉ I.σr ρ.1}

/-- The map `h_ρ` on domains: a point of `σ_ρ` goes to its image in `Dt`, any other point stays apart. -/
noncomputable def embed (ρ : Finset Dt) (hρ : ρ ∈ I.S) (x : I.Dr ρ) : I.GluedDom :=
  if hx : x ∈ I.σr ρ then Sum.inl (I.g ρ x) else Sum.inr ⟨⟨ρ, hρ⟩, ⟨x, hx⟩⟩

variable [Fintype Dt]

/-- `F` over `Pout` is the output of Construction 7.5, i.e. the gluing (Definition 4.36, Eq. (3), p.19): `Pout` consists
of the images of the elements of the pieces and of the images `h_i(P_i∗)` of the whole pieces; the local code at an image
is the image of the local code, and the local code at the image of a whole piece is the image of `F_i(P_i)`. `F` is a
sheaf (Proposition 4.37, p.20). -/
structure IsGluedOutput (Pout : CodedSpace I.GluedDom) (G : LocalCodes F I.GluedDom) : Prop where
  isSheaf : G.IsSheaf Pout
  mem_iff : ∀ τ : Finset I.GluedDom, τ ∈ Pout.P ↔
    (∃ τ₀ ∈ I.Pt.P, τ = τ₀.image Sum.inl) ∨
    τ = (Finset.univ : Finset Dt).image Sum.inl ∨
    (∃ (ρ : Finset Dt) (hρ : ρ ∈ I.S), ∃ α ∈ (I.Pr ρ).P, τ = α.image (I.embed ρ hρ)) ∨
    (∃ (ρ : Finset Dt) (hρ : ρ ∈ I.S), τ = Finset.univ.image (I.embed ρ hρ))
  code_t : ∀ τ₀ ∈ I.Pt.P,
    pullTo Sum.inl τ₀ '' (G.code (τ₀.image Sum.inl) : Set (I.GluedDom → F)) = (I.Ft.code τ₀ : Set (Dt → F))
  whole_t :
    pullTo Sum.inl Finset.univ '' (G.code ((Finset.univ : Finset Dt).image Sum.inl) : Set (I.GluedDom → F)) =
      I.Ft.sections I.Pt.P
  code_r : ∀ (ρ : Finset Dt) (hρ : ρ ∈ I.S), ∀ α ∈ (I.Pr ρ).P,
    pullTo (I.embed ρ hρ) α '' (G.code (α.image (I.embed ρ hρ)) : Set (I.GluedDom → F)) =
      ((I.Fr ρ).code α : Set (I.Dr ρ → F))
  whole_r : ∀ (ρ : Finset Dt) (hρ : ρ ∈ I.S),
    pullTo (I.embed ρ hρ) Finset.univ '' (G.code (Finset.univ.image (I.embed ρ hρ)) : Set (I.GluedDom → F)) =
      (I.Fr ρ).sections (I.Pr ρ).P

/-- The word `h_t(c)` on the glued domain, zero-padded. -/
def pushT (c : Dt → F) : I.GluedDom → F
  | Sum.inl x => c x
  | Sum.inr _ => 0

end GluingInput

end ZKSheafPCP


