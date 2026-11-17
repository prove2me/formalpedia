-- Prove2me | Definitions.Def_ManolescuPiccirillo_Kirby
-- name    : ManolescuPiccirillo_Kirby
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T18:49:58.559373+00:00
-- url     : https://prove2.me/theorems/91df0867-ed83-41a9-bab3-1af363687b7e
-- title:
--   Manolescu–Piccirillo: Kirby layer
-- statement:
--   Framed links, Reidemeister moves R1/R2/R3, band-sum splices, handle slides, and Kirby equivalence.
-- source:
--   Epoch AI FrontierMath, smooth 4D Poincaré conjecture, https://epoch.ai/frontiermath/open-problems/smooth-poincare-4d

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD

open Classical
noncomputable section

namespace ManolescuPiccirillo

structure FramedLink where
  pd : PD
  framings : List ℤ
  splitUnknotFramings : List ℤ

def FramedLink.zero (K : PD) : FramedLink := ⟨K, [0], []⟩

namespace PD

def ins (l : List (Fin 4 → ℕ)) (i : ℕ) (x : Fin 4 → ℕ) : List (Fin 4 → ℕ) :=
  l.take i ++ [x] ++ l.drop i

def spliceEntries (es : List ℕ) (x y u v : ℕ) : List ℕ :=
  (es.foldl (fun st : Bool × Bool × List ℕ => fun e =>
    let (sx, sy, acc) := st
    if e = x then (true, sy, acc ++ [if sx then v else u])
    else if e = y then (sx, true, acc ++ [if sy then u else v])
    else (sx, sy, acc ++ [e])) (false, false, [])).2.2

def ofEntries (es : List ℕ) : PD :=
  ⟨(List.range (es.length / 4)).map (fun k => fun j : Fin 4 => es[4 * k + j.val]!)⟩

def splice (D : PD) (x y u v : ℕ) : PD := ofEntries (spliceEntries D.entries x y u v)

def IsBandMerge (D D' : PD) : Prop :=
  ∃ x y u v : ℕ, x ∈ D.labels ∧ y ∈ D.labels ∧ x ≠ y ∧
    u ∉ D.labels ∧ v ∉ D.labels ∧ u ≠ v ∧
    D' = D.splice x y u v ∧ D'.numComponents + 1 = D.numComponents

def R1 (D D' : PD) : Prop :=
  ∃ (i : ℕ) (a b c : ℕ) (rest : List (Fin 4 → ℕ)),
    i ≤ rest.length ∧ D.crossings = ins rest i ![a, b, c, b] ∧
    (∀ c' ∈ rest, ∀ j, c' j ≠ b) ∧
    D'.crossings = rest.map (fun c' => fun j => if c' j = c then a else c' j)
  ∨ ∃ (i : ℕ) (a b c : ℕ) (rest : List (Fin 4 → ℕ)),
    i ≤ rest.length ∧ D'.crossings = ins rest i ![a, b, c, b] ∧
    (∀ c' ∈ rest, ∀ j, c' j ≠ b) ∧
    D.crossings = rest.map (fun c' => fun j => if c' j = c then a else c' j)

def R2 (D D' : PD) : Prop :=
  ∃ (i j : ℕ) (a b c d e f : ℕ) (rest : List (Fin 4 → ℕ)),
    i < j ∧ j ≤ rest.length + 1 ∧
    D.crossings = ins (ins rest i ![a, e, b, f]) j ![c, f, d, e] ∧
    (∀ c' ∈ rest, ∀ k, c' k ≠ e ∧ c' k ≠ f) ∧
    D'.crossings = rest.map (fun c' => fun k =>
      if c' k = b then a else if c' k = d then c else c' k)
  ∨ ∃ (i j : ℕ) (a b c d e f : ℕ) (rest : List (Fin 4 → ℕ)),
    i < j ∧ j ≤ rest.length + 1 ∧
    D'.crossings = ins (ins rest i ![a, e, b, f]) j ![c, f, d, e] ∧
    (∀ c' ∈ rest, ∀ k, c' k ≠ e ∧ c' k ≠ f) ∧
    D.crossings = rest.map (fun c' => fun k =>
      if c' k = b then a else if c' k = d then c else c' k)

def R3 (D D' : PD) : Prop :=
  ∃ (i j k : ℕ) (a b c d e f g h l : ℕ) (rest : List (Fin 4 → ℕ)),
    i < j ∧ j < k ∧ k ≤ rest.length + 2 ∧
    D.crossings = ins (ins (ins rest i ![a, b, c, d]) j ![e, f, g, h]) k ![l, c, f, a] ∧
    D'.crossings = ins (ins (ins rest i ![b, c, d, a]) j ![f, g, h, e]) k ![c, f, a, l]

inductive ReidemeisterEquiv : PD → PD → Prop
  | refl (D : PD) : ReidemeisterEquiv D D
  | step (D D' D'' : PD) : (R1 D D' ∨ R2 D D' ∨ R3 D D') → ReidemeisterEquiv D' D'' → ReidemeisterEquiv D D''
  | symm (D D' : PD) : ReidemeisterEquiv D D' → ReidemeisterEquiv D' D

end PD

/-- A handle slide: band-sum one component with a framed push-off of another. -/
def HandleSlide (L L' : FramedLink) : Prop :=
  ∃ (x y u v : ℕ) (Bcopy : PD),
    Bcopy.ReidemeisterEquiv L.pd ∧
    L'.pd.ReidemeisterEquiv (L.pd.splice x y u v) ∧
    L'.splitUnknotFramings = L.splitUnknotFramings ∧
    L'.framings.length = L.framings.length

inductive KirbyMove : FramedLink → FramedLink → Prop
  | r1 (L L' : FramedLink) : L.pd.R1 L'.pd → L.framings = L'.framings →
      L.splitUnknotFramings = L'.splitUnknotFramings → KirbyMove L L'
  | r2 (L L' : FramedLink) : L.pd.R2 L'.pd → L.framings = L'.framings →
      L.splitUnknotFramings = L'.splitUnknotFramings → KirbyMove L L'
  | r3 (L L' : FramedLink) : L.pd.R3 L'.pd → L.framings = L'.framings →
      L.splitUnknotFramings = L'.splitUnknotFramings → KirbyMove L L'
  | pm1 (L : FramedLink) (ε : ℤ) : ε = 1 ∨ ε = -1 →
      KirbyMove L ⟨L.pd, L.framings, ε :: L.splitUnknotFramings⟩
  | handleSlide (L L' : FramedLink) : HandleSlide L L' → KirbyMove L L'

inductive KirbyEquivalent : FramedLink → FramedLink → Prop
  | refl (L : FramedLink) : KirbyEquivalent L L
  | step (L L' L'' : FramedLink) : KirbyMove L L' → KirbyEquivalent L' L'' → KirbyEquivalent L L''
  | symm (L L' : FramedLink) : KirbyEquivalent L L' → KirbyEquivalent L' L

end ManolescuPiccirillo


