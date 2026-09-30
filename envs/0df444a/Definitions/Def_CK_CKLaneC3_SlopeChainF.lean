-- Prove2me | Definitions.Def_CK_CKLaneC3_SlopeChainF
-- name    : CK_CKLaneC3_SlopeChainF
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:50:30.372622+00:00
-- url     : https://prove2.me/theorems/352bde6e-a410-41a3-bea7-53f3b51ea58a
-- title:
--   Courtade–Kumar proof module `CKLaneC3.SlopeChainF` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.SlopeChainF` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.SlopeChainF` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.SlopeChainF (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/SlopeChainF.lean)

import Definitions.Def_CK_CKLaneC3_SlopeChain

-- ===== source module CKLaneC3.SlopeChainF =====
section

/-!
# Lane C3 — memoised slope chains (a semantics-preserving kernel optimisation)

`chainJetF T F` computes exactly what `chainJet T` computes, except that a chain piece `p`
whose sub-range starts at `p.y0` (every interior piece of a contiguous chain) takes the jet
`pieceJet p p.y0 p.y1` from a precomputed table `F` instead of re-evaluating the Taylor form.
Under `FullValid T F` (each stored jet *equals* the recomputed one, checked once per piece)
we prove `chainJetF T F = chainJet T`; the certificate semantics is unchanged and only the
per-cell kernel work drops.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.SlopeChainF

open GeneralCK GeneralCK.Certificates
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain

/-- A chunked table of full-piece jets, aligned with a piece table. -/
abbrev JTable := List (List (DyadicJet5Enclosure P))

def getFull (F : JTable) (r : ℕ × ℕ) : Option (DyadicJet5Enclosure P) :=
  match F[r.1]? with
  | some c => c[r.2]?
  | none => none

/-- `j` is the full-piece Taylor jet of `p`. -/
abbrev FullRel (p : Piece) (j : DyadicJet5Enclosure P) : Prop := j = pieceJet p p.y0 p.y1

/-- Every stored jet equals the recomputed full-piece jet of the aligned piece. -/
def FullValid (T : List (List Piece)) (F : JTable) : Prop :=
  ∀ r p j, getPiece T r = some p → getFull F r = some j → FullRel p j

theorem forall2_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ {i : ℕ} {a : α} {b : β}, l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h1, _ => by simp at h1
  | _, _, .cons hab _, 0, _, _, h1, h2 => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hab
  | _, _, .cons _ hrest, i + 1, _, _, h1, h2 => by
      simp only [List.getElem?_cons_succ] at h1 h2
      exact forall2_getElem? hrest h1 h2

theorem fullValid_of_forall2 {T : List (List Piece)} {F : JTable}
    (h : List.Forall₂ (List.Forall₂ FullRel) T F) : FullValid T F := by
  intro r p j hp hj
  unfold getPiece at hp
  unfold getFull at hj
  cases hc : T[r.1]? with
  | none => rw [hc] at hp; exact absurd hp (by simp)
  | some c =>
    cases hf : F[r.1]? with
    | none => rw [hf] at hj; exact absurd hj (by simp)
    | some f =>
      rw [hc] at hp
      rw [hf] at hj
      exact forall2_getElem? (forall2_getElem? h hc hf) hp hj

/-- Jet of a chain piece on `[lo, p.y1]`; memoised when `lo = p.y0`. -/
def firstJet (F : JTable) (r : ℕ × ℕ) (p : Piece) (lo : ℚ) : DyadicJet5Enclosure P :=
  if lo = p.y0 then
    match getFull F r with
    | some j => j
    | none => pieceJet p lo p.y1
  else pieceJet p lo p.y1

theorem firstJet_eq {T : List (List Piece)} {F : JTable} (hF : FullValid T F) {r : ℕ × ℕ}
    {p : Piece} (hp : getPiece T r = some p) (lo : ℚ) :
    firstJet F r p lo = pieceJet p lo p.y1 := by
  unfold firstJet
  split_ifs with h
  · cases hj : getFull F r with
    | none => rfl
    | some j =>
      subst h
      exact hF r p j hp hj
  · rfl

/-- `chainJet` with memoised interior pieces. -/
def chainJetF (T : List (List Piece)) (F : JTable) :
    List (ℕ × ℕ) → ℚ → ℚ → Option (DyadicJet5Enclosure P)
  | [], _, _ => none
  | [r], lo, hi =>
    match getPiece T r with
    | some p => if p.y0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ p.y1 then some (pieceJet p lo hi) else none
    | none => none
  | r :: r' :: rs, lo, hi =>
    match getPiece T r with
    | some p =>
      if p.y0 ≤ lo ∧ lo ≤ p.y1 ∧ p.y1 < hi then
        match chainJetF T F (r' :: rs) p.y1 hi with
        | some J => some (hullJ (firstJet F r p lo) J)
        | none => none
      else none
    | none => none

theorem chainJetF_eq {T : List (List Piece)} {F : JTable} (hF : FullValid T F) :
    ∀ (refs : List (ℕ × ℕ)) (lo hi : ℚ), chainJetF T F refs lo hi = chainJet T refs lo hi := by
  intro refs
  induction refs with
  | nil => intro lo hi; simp [chainJetF, chainJet]
  | cons r rs ih =>
    intro lo hi
    cases rs with
    | nil =>
      simp only [chainJetF, chainJet]
      cases getPiece T r <;> rfl
    | cons r' rs' =>
      simp only [chainJetF, chainJet]
      cases hp : getPiece T r with
      | none => rfl
      | some p =>
        simp only [ih, firstJet_eq hF hp]
        cases chainJet T (r' :: rs') p.y1 hi <;> rfl

theorem chainJetF_fun {T : List (List Piece)} {F : JTable} (hF : FullValid T F) :
    chainJetF T F = chainJet T :=
  funext fun refs => funext fun lo => funext fun hi => chainJetF_eq hF refs lo hi

end CKLaneC3.SlopeChainF

#print axioms CKLaneC3.SlopeChainF.fullValid_of_forall2
#print axioms CKLaneC3.SlopeChainF.chainJetF_fun

end


