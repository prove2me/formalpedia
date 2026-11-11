-- Prove2me | Definitions.Def_FullImmersionFPT_Main_Decorated
-- name    : FullImmersionFPT_Main_Decorated
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:48:04.553455+00:00
-- url     : https://prove2.me/theorems/e302cb0c-2797-4f1b-8c55-368314087d05
-- title:
--   Decorated graphs, their full immersions (§13.2), equivalence, color-folios, folios and splitting off at a decorated vertex
-- statement:
--   A **decorated graph** $\mathcal G=(G,\lambda,R,\rho,\alpha)$ consists of a connected 4-regular graph $G$, an $\mathbb F_2^U$-labeling $\lambda$ of its edges ($|U|=d$), roots $R\subseteq V(G)$ with an injective $\rho:R\to\mathbb N$, and a $q$-coloring $\alpha$ assigning to every half-edge a subset of $\{1,\dots,q\}$. It is **colorless** if every color set is empty. Two decorated graphs are **equivalent** if one is obtained from the other by shiftings, up to an isomorphism preserving labels, colors and the $\rho$-values of roots.
--
--   $\mathcal H=(H,\mu,R_H,\rho_H,\beta)$ is a **full immersion** of $\mathcal G$ (§13.2) if there are shiftings $\lambda'$ of $\lambda$ and $\mu'$ of $\mu$ such that (1) $\rho_H(R_H)=\rho_G(R_G)$; (2) an injective $\varphi:V(H)\to V(G)$ has $\rho_G(\varphi(v))=\rho_H(v)$ for every root $v$ of $H$; (3) every edge $uv$ of $H$ with half-edges $h_1$ at $u$ and $h_2$ at $v$ is mapped to a $\varphi(u)\varphi(v)$-trail $T$ of $G$ with $\lambda'(T)=\mu'(uv)$, forward colors containing $\beta(h_1)$ and backward colors containing $\beta(h_2)$, the trails being edge-disjoint; and (4) every edge of $G$ lies in exactly one of these trails.
--
--   The **$\tau$-color-folio** $C_\tau(\mathcal G)$ is the set of decorated graphs $\mathcal F$, up to equivalence, fully immersed by $\mathcal G$, with $|V(\mathcal F)|\le\tau$, in which every edge has at most one half-edge with a non-empty color set and that set is a single color. For a colorless $\mathcal G$ without parent edge, the **folio** $P(\mathcal G)$ is the set of colorless decorated graphs, up to equivalence, with at most $\delta_0$ vertices that $\mathcal G$ fully immerses.
--
--   **Splitting off** at a non-root vertex $v$ (§18.1) uses one of the three pairings of the four half-edges at $v$ (never the two halves of a loop): labels are added and the colors of the joined half-edges merged (the half-edge replacing $h_1'$ gets $\alpha(h_1')\cup\alpha(h_2)$); roots are unchanged. A vertex $v$ is **irrelevant for the $\tau$-color-folio** if it is a non-root vertex and for each decorated graph $\mathcal G'$ obtained by splitting off at $v$, $C_\tau(\mathcal G')=C_\tau(\mathcal G)$.
--
--   **Formalization Note.** `Decorated V H d q` holds a `Multigraph`, labels `H → (Fin d → ZMod 2)`, `root : V → Option ℕ` (`none` off $R$) and colors `H → Finset (Fin q)`. In `FullyImmerses`, the edge with half-edges `h` and `mate h` of $\mathcal F$ maps to the non-empty trail `T h`, `T (mate h)` is its reversal, and (4) with edge-disjointness is "every half-edge of $G$ is a tail half-edge of exactly one `T h`". Shiftings are sequences of `shiftAt`. Colorless graphs are those with `q = 0`. Folios and color-folios are output as a list of codes (`DecoCode.words`: $n,m,d,q$, per edge its ends, label bits and the color bits of both half-edges, per vertex its root value or $-1$); `EmitsUpToEquiv` says every listed graph belongs to the set and every member of the set (on any types) is equivalent to a listed one.
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), pp. 29–31 (§§13.1–13.2), p. 31 (§14, color-folios), p. 56 (§18.1), p. 71 (§19.2, folios)

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Machine

set_option autoImplicit false

/-!
# Decorated graphs, their full immersions, color-folios and folios (§13.1–13.2, pp. 29–31; §14,
p. 31; §18.1, p. 56; §19.2, p. 71)

Barabash, Geelen, McCarty, McFarland, Wollan, *Finding full immersions is fixed-parameter
tractable in labeled tour graphs* (STOC 2027 submission, manuscript of November 2, 2026).

* A **decorated graph** `(G, λ, R, ρ, α)`: `G` a connected 4-regular graph, `λ` an `F₂^U`-labeling
  of its edges, roots `R ⊆ V(G)` with an injective `ρ : R → ℕ`, and a `q`-coloring `α` mapping each
  half-edge to a subset of `[q]`. Here `|U| = d`, `F₂^U = Fin d → ZMod 2`, `[q] = Fin q`, and
  `ρ : V → Option ℕ` (`none` off the roots).
* **Shifting** at `X` adds a vector of `F₂^U` to the labels of `δ(X)`; two decorated graphs are
  **equivalent** if one is obtained from the other by shiftings, up to an isomorphism preserving
  `ρ`-values of roots and colors.
* **Full immersion** (§13.2): `H` is a full immersion of `G` if there are shiftings `λ′` of `λ` and
  `μ′` of `μ` such that (1) `ρ_H(R_H) = ρ_G(R_G)`; (2) an injective `ϕ : V(H) → V(G)` with
  `ρ_G(ϕ(v)) = ρ_H(v)` for `v ∈ R_H`; (3) each edge `uv` of `H` with half-edges `h₁` at `u`, `h₂` at
  `v` maps to a `ϕ(u)ϕ(v)`-trail `T` with `λ′(T) = μ′(uv)`, forward colors `⊇ β(h₁)`, backward colors
  `⊇ β(h₂)`, the trails edge-disjoint; (4) every edge of `G` lies in exactly one trail.
* The **color-folio** `C_τ(G)`: the decorated graphs `F` (up to equivalence) fully immersed by `G`
  in which every edge has at most one half-edge with a non-empty color set, that set being a single
  color, and `|V(F)| ≤ τ`.
* The **folio** `P(G)` of a colorless decorated graph `G` (no parent edge, §19.2): the colorless
  decorated graphs `F` (up to equivalence) with at most `δ₀` vertices that `G` fully immerses.
* **Splitting off** at a non-root vertex (§18.1): `Multigraph.splitOff`, with labels added
  (`splitLabel`) and colors merged (`splitColor`); roots unchanged.

A colorless decorated graph is one with `q = 0` colors (every color set is empty).
-/

namespace FullImmersionFPT.Main

open Classical

noncomputable section

/-- A decorated graph on ambient types `V`, `H`, labels in `F₂^d`, colors in `Fin q`. -/
structure Decorated (V H : Type) (d q : ℕ) where
  G : Multigraph V H
  lab : H → (Fin d → ZMod 2)
  root : V → Option ℕ
  col : H → Finset (Fin q)

namespace Decorated

variable {V H : Type} {d q : ℕ}

/-- The decorated-graph conditions: `G` well-formed, connected and 4-regular; the two half-edges
of an edge carry its label; `ρ` injective on the roots. -/
def IsDecorated (D : Decorated V H d q) : Prop :=
  D.G.IsValid ∧ D.G.IsRegular 4 ∧ D.G.IsConnected ∧ (∀ h ∈ D.G.halves, D.lab (D.G.mate h) = D.lab h) ∧
    ∀ u ∈ D.G.verts, ∀ w ∈ D.G.verts, ∀ k : ℕ, D.root u = some k → D.root w = some k → u = w

/-- The set `R` of roots. -/
def roots (D : Decorated V H d q) : Finset V := D.G.verts.filter fun v => D.root v ≠ none

/-- The set `ρ(R)` of root values. -/
def rootValues (D : Decorated V H d q) : Set ℕ := {k | ∃ v ∈ D.G.verts, D.root v = some k}

/-- `H` is a full immersion of `G` (§13.2), i.e. `G` fully immerses `F`. The edge `uv` of `F` with
half-edges `h` (at `u`) and `mate h` (at `v`) maps to the trail `T h` from `ϕ(u)` to `ϕ(v)`, and
`T (mate h)` is its reversal; "every edge of `G` lies in exactly one trail" is: every half-edge of
`G` is a tail half-edge of exactly one `T h`. Trails are non-empty. -/
def FullyImmerses {V' H' : Type} (D : Decorated V H d q) (F : Decorated V' H' d q) : Prop :=
  ∃ (lab' : H → (Fin d → ZMod 2)) (mu' : H' → (Fin d → ZMod 2)),
    D.G.IsShiftingOf D.lab lab' ∧ F.G.IsShiftingOf F.lab mu' ∧
    F.rootValues = D.rootValues ∧
    ∃ (φ : V' → V) (T : H' → List H),
      Set.InjOn φ ↑F.G.verts ∧ (∀ v ∈ F.G.verts, φ v ∈ D.G.verts) ∧
      (∀ v ∈ F.G.verts, ∀ k : ℕ, F.root v = some k → D.root (φ v) = some k) ∧
      (∀ h ∈ F.G.halves,
        D.G.IsTrailFrom (T h) (φ (F.G.inc h)) (φ (F.G.inc (F.G.mate h))) ∧
        T (F.G.mate h) = D.G.rev (T h) ∧
        Multigraph.trailSum lab' (T h) = mu' h ∧
        F.col h ⊆ Multigraph.fwdColor D.col (T h) ∧
        F.col (F.G.mate h) ⊆ D.G.bwdColor D.col (T h)) ∧
      ∀ g ∈ D.G.halves, ∃! h, h ∈ F.G.halves ∧ g ∈ T h

/-- An isomorphism of decorated graphs: bijections of vertices and half-edges commuting with `inc`
and `mate`, preserving labels, colors and root values. -/
def IsIso {V' H' : Type} (D : Decorated V H d q) (F : Decorated V' H' d q) : Prop :=
  ∃ (φ : V → V') (ψ : H → H'), Set.BijOn φ ↑D.G.verts ↑F.G.verts ∧
    Set.BijOn ψ ↑D.G.halves ↑F.G.halves ∧
    (∀ h ∈ D.G.halves, F.G.inc (ψ h) = φ (D.G.inc h) ∧ F.G.mate (ψ h) = ψ (D.G.mate h) ∧
      F.lab (ψ h) = D.lab h ∧ F.col (ψ h) = D.col h) ∧
    ∀ v ∈ D.G.verts, F.root (φ v) = D.root v

/-- `D` and `F` are equivalent: `F` is isomorphic to a decorated graph obtained from `D` by a
sequence of shiftings. -/
def Equivalent {V' H' : Type} (D : Decorated V H d q) (F : Decorated V' H' d q) : Prop :=
  ∃ lab' : H → (Fin d → ZMod 2), D.G.IsShiftingOf D.lab lab' ∧ IsIso { D with lab := lab' } F

/-- `F` belongs to the `τ`-color-folio `C_τ(D)` (§14, p. 31): `F` is a decorated graph with at
most `τ` vertices, every edge of `F` has at most one half-edge with a non-empty color set and that
set is a single color, and `D` fully immerses `F`. -/
def InColorFolio {V' H' : Type} (τ : ℕ) (D : Decorated V H d q) (F : Decorated V' H' d q) : Prop :=
  F.IsDecorated ∧ F.G.verts.card ≤ τ ∧
    (∀ h ∈ F.G.halves, F.col h = ∅ ∨ F.col (F.G.mate h) = ∅) ∧
    (∀ h ∈ F.G.halves, F.col h = ∅ ∨ (F.col h).card = 1) ∧
    D.FullyImmerses F

/-- `F` belongs to the folio `P(D)` of a colorless decorated graph `D` without parent edge
(§19.2, p. 71): `F` is a colorless decorated graph with at most `δ₀` vertices fully immersed by
`D`. (Colorless: `q = 0`.) -/
def InFolio {V' H' : Type} (δ₀ : ℕ) (D : Decorated V H d 0) (F : Decorated V' H' d 0) : Prop :=
  F.IsDecorated ∧ F.G.verts.card ≤ δ₀ ∧ D.FullyImmerses F

/-- Splitting off at the vertex `v` with the pairing `π` (§18.1): the graph `splitOff`, labels
`splitLabel`, colors `splitColor`, roots unchanged (`v` is required to be a non-root vertex
wherever this is used). -/
def splitOff (D : Decorated V H d q) (v : V) (π : H → H) : Decorated V H d q where
  G := D.G.splitOff v π
  lab := D.G.splitLabel v π D.lab
  root := D.root
  col := D.G.splitColor v π D.col

/-- The decorated graphs obtained by splitting off at `v`: `v` is a non-root vertex and `π` is a
pairing of the four half-edges at `v` that does not pair the two halves of a loop or of a 2-edge
cut. -/
def IsSplitAt (D : Decorated V H d q) (v : V) (π : H → H) : Prop :=
  v ∈ D.G.verts ∧ D.root v = none ∧ D.G.IsPairingAt v π ∧ D.G.IsLegalPairing v π

/-- `v` is irrelevant for the `τ`-color-folio (Propositions 25 and 44): `v` is a non-root vertex
of `D`, and for every one of the (three) decorated graphs `D′` obtained by splitting off at `v`, a
decorated graph `F` is in the `τ`-color-folio of `D` if and only if it is in that of `D′`. -/
def IsFolioIrrelevant (τ : ℕ) (D : Decorated V H d q) (v : V) : Prop :=
  v ∈ D.G.verts ∧ D.root v = none ∧
    ∀ π : H → H, D.IsSplitAt v π → ∀ (V' H' : Type) (F : Decorated V' H' d q),
      InColorFolio τ D F ↔ InColorFolio τ (D.splitOff v π) F

end Decorated

/-! ## Codes -/

/-- A decorated graph as an edge list on `Fin n`: ends, labels, the colors of the two half-edges
of every edge, and the root value (if any) of every vertex. -/
structure DecoCode (n m d q : ℕ) where
  ends : Fin m → Fin 2 → Fin n
  lab : Fin m → Fin d → ZMod 2
  col : Fin m → Fin 2 → Finset (Fin q)
  root : Fin n → Option ℕ

namespace DecoCode

variable {n m d q : ℕ}

/-- The decorated graph of the code. -/
def toDeco (K : DecoCode n m d q) : Decorated (Fin n) (Fin m × Fin 2) d q where
  G := ofEnds K.ends
  lab p := K.lab p.1
  root := K.root
  col p := K.col p.1 p.2

/-- The words: `n, m, d, q`; per edge its two ends, its `d` label bits and the `q` color bits of
each of its two half-edges; per vertex its root value, or `−1` if it is not a root. -/
def words (K : DecoCode n m d q) : List ℤ :=
  [(n : ℤ), (m : ℤ), (d : ℤ), (q : ℤ)] ++
    ((List.finRange m).flatMap fun e =>
      [((K.ends e 0 : ℕ) : ℤ), ((K.ends e 1 : ℕ) : ℤ)] ++ vecWords (K.lab e) ++
        setWords (K.col e 0) ++ setWords (K.col e 1)) ++
    (List.finRange n).map fun v => ((K.root v).map (fun k : ℕ => (k : ℤ))).getD (-1)

end DecoCode

/-- A list of decorated-graph codes (with their sizes `n, m`). -/
abbrev DecoList (d q : ℕ) := List (Σ p : ℕ × ℕ, DecoCode p.1 p.2 d q)

/-- The words of a list of codes: its length, then each code. -/
def decoListWords {d q : ℕ} (L : DecoList d q) : List ℤ :=
  (L.length : ℤ) :: L.flatMap fun K => K.2.words

/-- The output cells hold a list of codes that is the set `P` up to equivalence: every listed graph
belongs to `P`, and every decorated graph (on any types) belonging to `P` is equivalent to a listed
one. -/
def EmitsUpToEquiv {d q : ℕ} (out : ℕ → ℤ)
    (P : ∀ {V' H' : Type}, Decorated V' H' d q → Prop) : Prop :=
  ∃ L : DecoList d q, FOMCMonDep.Emits out (decoListWords L) ∧ (∀ K ∈ L, P K.2.toDeco) ∧
    ∀ (V' H' : Type) (F : Decorated V' H' d q), P F → ∃ K ∈ L, K.2.toDeco.Equivalent F

end

end FullImmersionFPT.Main


