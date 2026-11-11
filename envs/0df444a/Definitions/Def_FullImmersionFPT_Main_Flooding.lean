-- Prove2me | Definitions.Def_FullImmersionFPT_Main_Flooding
-- name    : FullImmersionFPT_Main_Flooding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:47:56.185149+00:00
-- url     : https://prove2.me/theorems/3e0206e0-0077-4680-9d0b-b7f6905abcfd
-- title:
--   Free and signed graphs, floodings, certificates, forced edges, Assumption 12, candidates and dictionaries (§3, §§5–7)
-- statement:
--   A **free graph** $\mathcal G=(G,\Sigma,F,t)$ consists of an Eulerian graph $G$, a set $\Sigma\subseteq E(G)$ (the **signature**), a set $F\subseteq E(G)$ of **free** edges ($\Sigma$ and $F$ may intersect) and a root $t\in V(G)$; a **signed graph** is a free graph with $F=\emptyset$. A circuit is **feasible** if it contains a free edge or an odd number of signature edges. A $t$-**circuit** is a circuit beginning and ending at $t$ that does not otherwise visit $t$. A **flooding** is a collection of $\deg(t)/2$ $t$-circuits partitioning $E(G)$ (reversing circuits gives the same flooding); its **value** is the number of its feasible circuits; $\nu(\mathcal G)$ is the maximum value and a flooding attaining it is **optimal**.
--
--   A **shifting** of $\Sigma$ is $\Sigma'=\Sigma\,\Delta\,\delta(S)$. A **certificate** is $(X,\Sigma')$ with $t\in X\subseteq V(G)$ and $\Sigma'$ a shifting of $\Sigma$. A component $K$ of $G-X$ is $\Sigma'$-**odd** if no free edge is incident to $V(K)$ and the number of edges incident to $V(K)$ and in $\Sigma'$ differs from $|\delta(K)|/2$ modulo 2; $\mathrm{odd}_{\Sigma'}(G-X)$ counts them; $E_{F,\Sigma'}(X)$ is the set of edges with both ends in $X$ that are free or in $\Sigma'$, and
--   $$\mathrm{value}(X,\Sigma') = |E_{F,\Sigma'}(X)| + \tfrac12|\delta(X)| - \mathrm{odd}_{\Sigma'}(G-X).$$
--   An edge is **forced** by $(X,\Sigma')$ if it is in $E_{F,\Sigma'}(X)$ or incident to a component of $G-X$ that is not $\Sigma'$-odd.
--
--   **Assumption 12**: a program that, given a signed graph with $m$ edges and a flooding $\mathcal C$, finds within $\varphi(m)$ steps either a flooding of greater value or a certificate of the same value as $\mathcal C$ such that every edge not forced by it lies in an infeasible circuit of some optimal flooding.
--
--   In a signed graph, the **label** of an edge is 1 if it is in $\Sigma$ and 0 otherwise. A **candidate** is $(\vec f,\alpha)$ with $\alpha\in\{0,1\}$, $\alpha=0$ if the tail of $\vec f$ is $t$, and $\alpha$ the label of $f$ if its head is $t$; it is equivalent to $(\vec f^{-1},\alpha+\mathrm{label}(f))$. It **represents** a circuit $C$ if $C$ is even and, after possibly reversing $C$, $C$ contains $\vec f$ and the label of the part of $C$ before $\vec f$ is $\alpha$; it is **displayed** by a set of floodings $D$ if it represents a circuit of a flooding in $D$. A **dictionary** is a non-empty set of floodings of equal value whose size is at most one plus the number of candidates (up to equivalence) it displays. $D'$ **improves** $D$ if it has greater value, or the same value and displays more candidates. A certificate **respects** $D$ if it has the value of $D$ and every edge not forced by it is displayed by $D$ (some candidate containing it is displayed).
--
--   **Formalization Note.** Edge sets are `Finset (Sym2 H)`; `S'` stands for $\Sigma'$ (Lean reserves `Σ`). A flooding is a list of circuits whose arcs and reversed arcs, together, are a permutation of all half-edges; $\nu\le\ell$ is stated as "every flooding has value $\le\ell$". Dictionaries are lists of pairwise inequivalent floodings (equivalence: same circuits up to reversal and order). `certValue` is an integer with exact division ($|\delta(X)|$ is even in an Eulerian graph). Codes: a free graph is written $n,m,t$ then per edge its two ends, its signature bit and its free bit; a flooding as its number of circuits and its circuits; a certificate as the membership bits of $X$ and of $\Sigma'$; a dictionary as its size and its floodings.
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 5 (§1), p. 8 (§3), pp. 13–14 (§5), p. 15 (Assumption 12), pp. 17–18 (§7)

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Machine

set_option autoImplicit false

/-!
# Free graphs, floodings, certificates and dictionaries (§1 p. 5; §3 p. 8; §5 pp. 13–14; §6 p. 15;
§7 pp. 17–18)

Barabash, Geelen, McCarty, McFarland, Wollan, *Finding full immersions is fixed-parameter
tractable in labeled tour graphs* (STOC 2027 submission, manuscript of November 2, 2026).

* A **free graph** `(G, Σ, F, t)`: `G` Eulerian (connected, every degree even), the signature `Σ`
  and the free edges `F` arbitrary sets of edges (they may intersect), the root `t`. A **signed
  graph** is a free graph with `F = ∅`.
* A circuit is **feasible** if it contains a free edge or an odd number of signature edges. A
  **`t`-circuit** begins and ends at `t` and does not otherwise visit `t`. A **flooding** is a
  collection of `degree(t)/2` `t`-circuits partitioning `E(G)`; its **value** is its number of
  feasible circuits; an **optimal** flooding has maximum value (`ν(G)`).
* A **certificate** `(X, Σ′)`: `t ∈ X ⊆ V(G)` and `Σ′ = Σ Δ δ(S)` a shifting of `Σ`. A component
  `K` of `G − X` is **`Σ′`-odd** if no free edge is incident to `V(K)` and the number of edges
  incident to `V(K)` and in `Σ′` differs from `|δ(K)|/2` modulo 2;
  `value(X, Σ′) = |E_{F,Σ′}(X)| + |δ(X)|/2 − odd_{Σ′}(G − X)`. An edge is **forced** by `(X, Σ′)`
  if it is in `E_{F,Σ′}(X)` or incident to a component of `G − X` that is not `Σ′`-odd.
* Candidates, representation, display, **dictionaries**, improvement and respect (§7).

Conventions. A circuit is a list of tail half-edges (see `Multigraph.IsTrail`); a flooding is a
list of circuits (reversing circuits or reordering the list gives an equivalent flooding, which
has the same value). Certificate values are integers; `|δ(X)|` is even in an Eulerian graph, so
the integer division `/ 2` is exact.
-/

namespace FullImmersionFPT.Main

open Classical

noncomputable section

/-- A free graph `(G, Σ, F, t)` on ambient types `V`, `H`. -/
structure FreeGraph (V H : Type) where
  G : Multigraph V H
  sig : Finset (Sym2 H)
  free : Finset (Sym2 H)
  root : V

namespace FreeGraph

variable {V H : Type} (Γ : FreeGraph V H)

/-- `Γ` is a free graph: `G` is a well-formed Eulerian multigraph, `Σ, F ⊆ E(G)`, `t ∈ V(G)`. -/
def IsFree : Prop :=
  Γ.G.IsValid ∧ Γ.G.IsEulerian ∧ Γ.sig ⊆ Γ.G.edges ∧ Γ.free ⊆ Γ.G.edges ∧ Γ.root ∈ Γ.G.verts

/-- `Γ` is a signed graph: a free graph with no free edges. -/
def IsSigned : Prop := Γ.IsFree ∧ Γ.free = ∅

/-- The label (`1` if in the signature `Σ`, else `0`) of the edge of the half-edge `h`. -/
def lab (S' : Finset (Sym2 H)) (h : H) : ZMod 2 := if Γ.G.edgeOf h ∈ S' then 1 else 0

/-- The number of signature edges (w.r.t. `S'`) of a trail. -/
def sigCount (S' : Finset (Sym2 H)) (T : List H) : ℕ := (T.filter fun h => Γ.G.edgeOf h ∈ S').length

/-- A `t`-circuit: a non-empty trail that begins and ends at the root `t` and does not otherwise
visit `t`. -/
def IsTCircuit (T : List H) : Prop :=
  Γ.G.IsTrailFrom T Γ.root Γ.root ∧
    ∀ (i : ℕ) (hi : i < T.length), 0 < i → Γ.G.inc (T[i]'hi) ≠ Γ.root

/-- A circuit is feasible if it contains at least one free edge or an odd number of signature
edges (or both). -/
def IsFeasible (T : List H) : Prop :=
  (∃ h ∈ T, Γ.G.edgeOf h ∈ Γ.free) ∨ Odd (Γ.sigCount Γ.sig T)

/-- A flooding: a collection of `degree(t)/2` `t`-circuits partitioning `E(G)` (every half-edge of
`G` occurs exactly once among the circuits' arcs and their reversals). -/
def IsFlooding (C : List (List H)) : Prop :=
  (∀ T ∈ C, Γ.IsTCircuit T) ∧ 2 * C.length = Γ.G.deg Γ.root ∧
    (C.flatMap fun T => T ++ T.map Γ.G.mate).Perm Γ.G.halves.toList

/-- The value of a flooding: its number of feasible circuits. -/
def floodValue (C : List (List H)) : ℕ := (C.filter fun T => decide (Γ.IsFeasible T)).length

/-- An optimal flooding: a flooding of maximum value (value `ν(G)`). -/
def IsOptimal (C : List (List H)) : Prop :=
  Γ.IsFlooding C ∧ ∀ C', Γ.IsFlooding C' → Γ.floodValue C' ≤ Γ.floodValue C

/-- `S'` is a shifting of `Σ`: `S' = Σ Δ δ(S)` for some vertex set `S`. -/
def IsShiftingOfSig (S' : Finset (Sym2 H)) : Prop := ∃ S : Finset V, S' = symmDiff Γ.sig (Γ.G.cut S)

/-- A certificate `(X, S')`: `t ∈ X ⊆ V(G)` and `S'` a shifting of `Σ`. -/
def IsCertificate (X : Finset V) (S' : Finset (Sym2 H)) : Prop :=
  X ⊆ Γ.G.verts ∧ Γ.root ∈ X ∧ Γ.IsShiftingOfSig S'

/-- The vertex sets of the components of `G − X`. -/
def comps (X : Finset V) : Finset (Finset V) :=
  (Γ.G.verts \ X).image fun u => (Γ.G.verts \ X).filter fun w => Γ.G.ConnectedIn ↑(Γ.G.verts \ X) u w

/-- The edges incident to the vertex set `K` (with at least one end in `K`). -/
def incidentEdges (K : Finset V) : Finset (Sym2 H) :=
  (Γ.G.halves.filter fun h => Γ.G.inc h ∈ K).image Γ.G.edgeOf

/-- A component `K` of `G − X` is `S'`-odd: no free edge is incident to `V(K)`, and the number of
edges incident to `V(K)` and in `S'` differs from `|δ(K)|/2` modulo 2. -/
def IsOddComp (S' : Finset (Sym2 H)) (K : Finset V) : Prop :=
  (∀ e ∈ Γ.incidentEdges K, e ∉ Γ.free) ∧
    (Γ.incidentEdges K ∩ S').card % 2 ≠ ((Γ.G.cut K).card / 2) % 2

/-- `odd_{S'}(G − X)`: the number of `S'`-odd components of `G − X`. -/
def oddCount (X : Finset V) (S' : Finset (Sym2 H)) : ℕ :=
  ((Γ.comps X).filter fun K => Γ.IsOddComp S' K).card

/-- `E_{F,S'}(X)`: the edges with both ends in `X` that are free or in `S'` (or both). -/
def EFS (X : Finset V) (S' : Finset (Sym2 H)) : Finset (Sym2 H) :=
  (Γ.G.halves.filter fun h => Γ.G.inc h ∈ X ∧ Γ.G.inc (Γ.G.mate h) ∈ X ∧
    (Γ.G.edgeOf h ∈ Γ.free ∨ Γ.G.edgeOf h ∈ S')).image Γ.G.edgeOf

/-- `value(X, S') = |E_{F,S'}(X)| + |δ(X)|/2 − odd_{S'}(G − X)`. -/
def certValue (X : Finset V) (S' : Finset (Sym2 H)) : ℤ :=
  ((Γ.EFS X S').card : ℤ) + ((Γ.G.cut X).card : ℤ) / 2 - (Γ.oddCount X S' : ℤ)

/-- The edge `e` is forced by `(X, S')`: it is in `E_{F,S'}(X)`, or it is incident to a component
of `G − X` which is not `S'`-odd. -/
def IsForced (X : Finset V) (S' : Finset (Sym2 H)) (e : Sym2 H) : Prop :=
  e ∈ Γ.EFS X S' ∨ ∃ K ∈ Γ.comps X, ¬ Γ.IsOddComp S' K ∧ e ∈ Γ.incidentEdges K

/-- The guarantee of Assumption 12 for a certificate `(X, S')`: every edge not forced by it lies in
an infeasible circuit of some optimal flooding. -/
def HasAssumption12Guarantee (X : Finset V) (S' : Finset (Sym2 H)) : Prop :=
  ∀ e ∈ Γ.G.edges, ¬ Γ.IsForced X S' e →
    ∃ C, Γ.IsOptimal C ∧ ∃ T ∈ C, (∃ h ∈ T, Γ.G.edgeOf h = e) ∧ ¬ Γ.IsFeasible T

/-! ## Candidates and dictionaries (§7, pp. 17–18), for signed graphs -/

/-- A candidate `(f⃗, α)`: `f⃗` an arc (named by its tail half-edge), `α ∈ {0,1}`; if the tail of
`f⃗` is `t` then `α = 0`, and if its head is `t` then `α` is the label of `f`. -/
def IsCandidate (c : H × ZMod 2) : Prop :=
  c.1 ∈ Γ.G.halves ∧ (Γ.G.inc c.1 = Γ.root → c.2 = 0) ∧
    (Γ.G.inc (Γ.G.mate c.1) = Γ.root → c.2 = Γ.lab Γ.sig c.1)

/-- The class of a candidate: `(f⃗, α)` is equivalent to `(f⃗⁻¹, α + label(f))`. -/
def candClass (c : H × ZMod 2) : Sym2 (H × ZMod 2) :=
  s(c, (Γ.G.mate c.1, c.2 + Γ.lab Γ.sig c.1))

/-- The prefix label at position `i` of a trail: the label of its first `i` arcs. -/
def prefixLabel (T : List H) (i : ℕ) : ZMod 2 := ((T.take i).map (Γ.lab Γ.sig)).sum

/-- `(f⃗, α)` represents the circuit `T`: `T` is even and, after possibly reversing `T`, it contains
the arc `f⃗` and the prefix label at `f⃗` is `α`. -/
def Represents (c : H × ZMod 2) (T : List H) : Prop :=
  Even (Γ.sigCount Γ.sig T) ∧
    ∃ T' ∈ [T, Γ.G.rev T], ∃ (i : ℕ) (hi : i < T'.length), T'[i] = c.1 ∧ Γ.prefixLabel T' i = c.2

/-- `(f⃗, α)` is displayed by the set of floodings `D`: it represents a circuit of some flooding
in `D`. -/
def Displayed (D : List (List (List H))) (c : H × ZMod 2) : Prop :=
  ∃ C ∈ D, ∃ T ∈ C, Γ.Represents c T

/-- The candidates displayed by `D`, up to equivalence. -/
def displayedClasses (D : List (List (List H))) : Finset (Sym2 (H × ZMod 2)) :=
  ((Γ.G.halves ×ˢ (Finset.univ : Finset (ZMod 2))).filter fun c =>
    Γ.IsCandidate c ∧ Γ.Displayed D c).image Γ.candClass

/-- The class of a flooding up to reversing circuits and reordering. -/
def floodClass (C : List (List H)) : Multiset (Sym2 (List H)) :=
  (C.map fun T => s(T, Γ.G.rev T) : Multiset (Sym2 (List H)))

/-- A dictionary: a non-empty set of floodings (pairwise inequivalent) of equal value whose size is
at most the number of candidates (up to equivalence) it displays plus one. -/
def IsDictionary (D : List (List (List H))) : Prop :=
  D ≠ [] ∧ (∀ C ∈ D, Γ.IsFlooding C) ∧ (∀ C ∈ D, ∀ C' ∈ D, Γ.floodValue C = Γ.floodValue C') ∧
    D.Pairwise (fun C C' => Γ.floodClass C ≠ Γ.floodClass C') ∧
    D.length ≤ (Γ.displayedClasses D).card + 1

/-- The value of a dictionary: the common value of its floodings. -/
def dictValue (D : List (List (List H))) : ℕ := (D.head?.map Γ.floodValue).getD 0

/-- `D'` improves `D`: greater value, or the same value and more displayed candidates. -/
def Improves (D' D : List (List (List H))) : Prop :=
  Γ.dictValue D < Γ.dictValue D' ∨
    (Γ.dictValue D' = Γ.dictValue D ∧ (Γ.displayedClasses D).card < (Γ.displayedClasses D').card)

/-- The edge `e` is displayed by `D` (in at least one way): some candidate containing `e⃗` or
`e⃗⁻¹` is displayed. -/
def EdgeDisplayed (D : List (List (List H))) (e : Sym2 H) : Prop :=
  ∃ h ∈ Γ.G.halves, Γ.G.edgeOf h = e ∧ ∃ α : ZMod 2, Γ.IsCandidate (h, α) ∧ Γ.Displayed D (h, α)

/-- The certificate `(X, S')` respects `D`: it has the value of `D` and every edge not forced by it
is displayed by `D`. -/
def Respects (X : Finset V) (S' : Finset (Sym2 H)) (D : List (List (List H))) : Prop :=
  Γ.certValue X S' = (Γ.dictValue D : ℤ) ∧ ∀ e ∈ Γ.G.edges, ¬ Γ.IsForced X S' e → Γ.EdgeDisplayed D e

end FreeGraph

/-! ## Codes -/

/-- A free graph given as an edge list on `Fin n` with `m` edges: signature and free bits per edge
and the root. -/
structure FreeCode (n m : ℕ) where
  ends : Fin m → Fin 2 → Fin n
  sig : Fin m → Bool
  free : Fin m → Bool
  root : Fin n

namespace FreeCode

variable {n m : ℕ}

/-- The free graph of the code. -/
def toFree (Φ : FreeCode n m) : FreeGraph (Fin n) (Fin m × Fin 2) where
  G := ofEnds Φ.ends
  sig := (Finset.univ.filter fun e => Φ.sig e = true).image edgeSym
  free := (Finset.univ.filter fun e => Φ.free e = true).image edgeSym
  root := Φ.root

/-- The words: `n, m, t`, then per edge its two ends, its signature bit and its free bit. -/
def words (Φ : FreeCode n m) : List ℤ :=
  [(n : ℤ), (m : ℤ), ((Φ.root : ℕ) : ℤ)] ++
    (List.finRange m).flatMap fun e =>
      [((Φ.ends e 0 : ℕ) : ℤ), ((Φ.ends e 1 : ℕ) : ℤ), bitWord (Φ.sig e = true),
        bitWord (Φ.free e = true)]

end FreeCode

/-- The words of a flooding: its number of circuits, then each circuit (`trailWords`). -/
def floodWords {m : ℕ} (C : List (List (Fin m × Fin 2))) : List ℤ :=
  (C.length : ℤ) :: C.flatMap trailWords

/-- The words of a certificate `(X, S')`: the `n` membership bits of `X`, then the `m` membership
bits of `S'`. -/
def certWords {n m : ℕ} (X : Finset (Fin n)) (S' : Finset (Sym2 (Fin m × Fin 2))) : List ℤ :=
  (List.finRange n).map (fun v => bitWord (v ∈ X)) ++
    (List.finRange m).map (fun e => bitWord (edgeSym e ∈ S'))

/-- The words of a dictionary: its number of floodings, then each flooding. -/
def dictWords {m : ℕ} (D : List (List (List (Fin m × Fin 2)))) : List ℤ :=
  (D.length : ℤ) :: D.flatMap floodWords

/-- The output of Theorem 3 / Theorem 13 on `(Φ, k)`: either `0` and a flooding of value at least
`k`, or `1`, a flooding and a certificate of equal value. -/
def FloodOrCertOutput {n m : ℕ} (Φ : FreeCode n m) (k : ℤ) (out : ℕ → ℤ) : Prop :=
  (∃ C, Φ.toFree.IsFlooding C ∧ k ≤ (Φ.toFree.floodValue C : ℤ) ∧
      FOMCMonDep.Emits out (0 :: floodWords C)) ∨
    ∃ C X S', Φ.toFree.IsFlooding C ∧ Φ.toFree.IsCertificate X S' ∧
      (Φ.toFree.floodValue C : ℤ) = Φ.toFree.certValue X S' ∧
      FOMCMonDep.Emits out (1 :: floodWords C ++ certWords X S')

/-- **Assumption 12** (p. 15) for the program `A` with word-size factor `b` and time bound `ϕ`:
given a signed graph `(G, Σ, t)` (`m` edges) and a flooding `C`, `A` finds within `ϕ(m)` steps
either a flooding `C'` of value greater than that of `C`, or a certificate `(X, S')` of the same
value as `C` such that every edge not forced by `(X, S')` lies in an infeasible circuit of some
optimal flooding. Input: the code of the signed graph followed by the flooding's words. -/
def Assumption12 (A : List TrulySubcubicAPSP.Instr) (b : ℕ) (ϕ : ℕ → ℕ) : Prop :=
  ∀ (n m : ℕ) (Φ : FreeCode n m) (C : List (List (Fin m × Fin 2))),
    Φ.toFree.IsSigned → Φ.toFree.IsFlooding C →
    ∀ W : ℕ, FOMCMonDep.WordSizeOK b (Φ.words ++ floodWords C) W →
      RunsWithin A W (ϕ m) (Φ.words ++ floodWords C) fun out =>
        (∃ C', Φ.toFree.IsFlooding C' ∧ Φ.toFree.floodValue C < Φ.toFree.floodValue C' ∧
            FOMCMonDep.Emits out (0 :: floodWords C')) ∨
          ∃ X S', Φ.toFree.IsCertificate X S' ∧
            Φ.toFree.certValue X S' = (Φ.toFree.floodValue C : ℤ) ∧
            Φ.toFree.HasAssumption12Guarantee X S' ∧ FOMCMonDep.Emits out (1 :: certWords X S')

end

end FullImmersionFPT.Main


