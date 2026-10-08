-- Prove2me | Definitions.Def_FourColourRSST_Ring_Setting
-- name    : FourColourRSST_Ring_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:22.094977+00:00
-- url     : https://prove2.me/theorems/f1b4da14-b320-402e-b8d7-eb92f85e7ba0
-- title:
--   §3, p. 7 — edge-colourings of a circuit, signed matchings, θ-fit, consistent sets; §6, p. 25 — equivalence; the classes of (6.3) and (6.4)
-- statement:
--   Let $R$ be a **circuit** of length $k$: a cycle with edges $e_1, \dots, e_k$ in order, consecutive edges (including $e_k, e_1$) sharing an end, and no repeated vertices or edges.
--
--   1. An **edge-colouring** of $R$ is a map $\kappa : E(R) \to \{-1, 0, 1\}$.
--   2. A **match** is an unordered pair $\{e, f\}$ of distinct edges; a **signed match** is a pair $(m, \mu)$ with $m$ a match and $\mu = \pm 1$.
--   3. A **signed matching** is a set $M$ of signed matches such that whenever $(\{e,f\},\mu)$ and $(\{e',f'\},\mu')$ are distinct members of $M$: (i) $\{e,f\} \cap \{e',f'\} = \emptyset$, and (ii) $e$ and $f$ lie in the same component of the graph obtained from $R$ by deleting $e'$ and $f'$. Write $E(M)$ for the set of edges belonging to some match of $M$.
--   4. For $\theta \in \{-1,0,1\}$, $\kappa$ **$\theta$-fits** $M$ if (i) $E(M) = \{e \in E(R) : \kappa(e) \neq \theta\}$, and (ii) for each $(\{e,f\},\mu) \in M$, $\kappa(e) = \kappa(f)$ if and only if $\mu = 1$.
--   5. A set $\mathcal C$ of edge-colourings is **consistent** if for every $\kappa \in \mathcal C$ and every $\theta \in \{-1,0,1\}$ there is a signed matching $M$ such that $\kappa$ $\theta$-fits $M$ **and** $\mathcal C$ contains every edge-colouring that $\theta$-fits $M$.
--   6. Edge-colourings $\kappa, \kappa'$ are **equivalent** if $\kappa'(e) = \lambda(\kappa(e))$ for all $e$, for some permutation $\lambda$ of $\{-1,0,1\}$.
--
--   For the circuit of length 5 and $i \neq j$, $\mathcal A_{ij}$ is the equivalence class of the edge-colouring with value $1$ on $e_i$, $-1$ on $e_j$ and $0$ elsewhere. Then
--   $$\mathcal C_i = \mathcal A_{ij} \cup \mathcal A_{ik} \cup \mathcal A_{jk},\qquad \mathcal D_i = \mathcal A_{ac} \cup \mathcal A_{ad} \cup \mathcal A_{bc} \cup \mathcal A_{bd},\qquad \mathcal E = \mathcal A_{12} \cup \mathcal A_{23} \cup \mathcal A_{34} \cup \mathcal A_{45} \cup \mathcal A_{15},$$
--   where $e_j, e_k$ are the two edges sharing an end with $e_i$, and $e_a, e_b, e_c, e_d$ are the edges other than $e_i$ in order along the path $R - e_i$ (so $a, b, c, d = i+1, i+2, i+3, i+4$ modulo 5). For the circuit of length 4, $\mathcal C_0, \mathcal C_1, \mathcal C_2, \mathcal C_3$ are the classes of $(0,0,0,0)$, $(0,1,1,0)$, $(0,1,0,1)$, $(0,0,1,1)$ (values listed on $e_1, \dots, e_4$).
--
--   These objects are the language of reducibility in the Robertson–Sanders–Seymour–Thomas proof of the Four-Colour Theorem: the lifts of the tri-colourings of a near-triangulation to its boundary ring always form a consistent set (their (3.1)), and Birkhoff's lemmas (6.3), (6.4) classify the consistent sets on rings of length 4 and 5.
--
--   **Formalization Note.** The circuit of length $k$ is `SimpleGraph.cycleGraph k` on `Fin k`; its edges are indexed by `Fin k`, edge $i$ being $\{i, i+1\}$. The paper's $e_i$ is edge $i-1$ (0-based), so $\mathcal A_{12}$ is `A 0 1`, $\mathcal A_{15}$ is `A 0 4`, $\mathcal A_{25}$ is `A 1 4`, $\mathcal A_{35}$ is `A 2 4`. Colours are `SignType`; an edge-colouring is `Fin k → SignType`. A match is an element of `Sym2 (Fin k)` (a pair of edge indices) that is not a diagonal, and $\mu \in$ `ℤˣ`. Condition (ii) is stated literally: the edges of $\{e', f'\}$ are deleted from the cycle graph and the vertex $e$ (an end of edge $e$, which survives the deletion by (i)) must be reachable from the vertex $f$; it is required for both orders of every distinct pair. `C5 i` uses edges $i-1$ and $i+1$, and `D5 i` uses $(a,b,c,d) = (i+1, i+2, i+3, i+4)$, all modulo 5. `A i i` is never used. Circuits of length at most 2 (parallel edges) are not representable as `cycleGraph`; the general-$k$ statements assume $k \ge 3$.
-- source:
--   Robertson, Sanders, Seymour and Thomas, The Four-Colour Theorem, J. Combin. Theory Ser. B 70 (1997), author's manuscript (rev. 16 January 1997), p. 3, §2 (circuits); p. 7, §3 (edge-colouring, signed matching, θ-fit, consistent); p. 25, §6 (equivalence, (6.3), (6.4))

import Mathlib

namespace FourColourRSST.Ring

/-!
Robertson, Sanders, Seymour and Thomas, *The Four-Colour Theorem* (1997):
§2, p. 3 (circuits), §3, p. 7 (edge-colourings, signed matchings, θ-fit, consistent sets),
§6, p. 25 (equivalence of edge-colourings; the classes of (6.3) and (6.4)).

The circuit `R` of length `k` is `SimpleGraph.cycleGraph k` on `Fin k`. Its edges are indexed by
`Fin k`: edge `i` is `s(i, i + 1)`. The paper's `e_i` (1-based) is edge `i - 1` (0-based).
-/

/-- Edge `i` of the circuit of length `k`: the edge joining the vertices `i` and `i + 1` of
`SimpleGraph.cycleGraph k`. -/
def edge {k : ℕ} [NeZero k] (i : Fin k) : Sym2 (Fin k) := s(i, i + 1)

/-- An edge-colouring of the circuit of length `k`: a map from its edges (indexed by `Fin k`)
to `{-1, 0, 1}` (`SignType`). -/
abbrev EdgeColouring (k : ℕ) := Fin k → SignType

/-- A signed match: an unordered pair of edge indices together with a sign `μ = ±1`
(an element of `ℤˣ`). The pair must consist of distinct edges; this is required in
`IsSignedMatching`. -/
abbrev SignedMatch (k : ℕ) := Sym2 (Fin k) × ℤˣ

/-- The graph obtained from the circuit `R = cycleGraph k` by deleting the edges of the
pair `m'` (of edge indices). -/
def ringMinus {k : ℕ} [NeZero k] (m' : Sym2 (Fin k)) : SimpleGraph (Fin k) :=
  (SimpleGraph.cycleGraph k).deleteEdges {x | ∃ e ∈ m', x = edge e}

/-- A signed matching in `R` (§3, p. 7): a set `M` of signed matches whose pairs consist of
distinct edges, such that for distinct `({e, f}, μ), ({e', f'}, μ') ∈ M`
(i) `{e, f} ∩ {e', f'} = ∅`, and
(ii) `e, f` belong to the same component of the graph obtained from `R` by deleting `e'` and
`f'` (stated with the end `e` of edge `e`, which survives the deletion by (i)). -/
def IsSignedMatching {k : ℕ} [NeZero k] (M : Set (SignedMatch k)) : Prop :=
  (∀ p ∈ M, ¬ p.1.IsDiag) ∧
  ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
    (∀ e ∈ p.1, e ∉ q.1) ∧ (∀ e ∈ p.1, ∀ f ∈ p.1, (ringMinus q.1).Reachable e f)

/-- `E(M)`: the set of edges covered by some signed match of `M`. -/
def edgesOf {k : ℕ} (M : Set (SignedMatch k)) : Set (Fin k) :=
  {e | ∃ p ∈ M, e ∈ p.1}

/-- `κ` `θ`-fits `M` (§3, p. 7): (i) `E(M) = {e : κ(e) ≠ θ}`, and (ii) for each
`({e, f}, μ) ∈ M`, `κ(e) = κ(f)` if and only if `μ = 1`. -/
def Fits {k : ℕ} (θ : SignType) (κ : EdgeColouring k) (M : Set (SignedMatch k)) : Prop :=
  edgesOf M = {e | κ e ≠ θ} ∧
  ∀ p ∈ M, ∀ e f : Fin k, p.1 = s(e, f) → (κ e = κ f ↔ p.2 = 1)

/-- A set `𝒞` of edge-colourings is consistent (§3, p. 7) if for every `κ ∈ 𝒞` and every
`θ ∈ {-1, 0, 1}` there is a signed matching `M` such that `κ` `θ`-fits `M`, and `𝒞` contains
every edge-colouring that `θ`-fits `M`. -/
def Consistent {k : ℕ} [NeZero k] (C : Set (EdgeColouring k)) : Prop :=
  ∀ κ ∈ C, ∀ θ : SignType, ∃ M : Set (SignedMatch k),
    IsSignedMatching M ∧ Fits θ κ M ∧ ∀ κ' : EdgeColouring k, Fits θ κ' M → κ' ∈ C

/-- Two edge-colourings are equivalent (§6, p. 25) if there is a permutation `σ` of
`{-1, 0, 1}` with `κ'(e) = σ(κ(e))` for every edge `e`. -/
def Equivalent {k : ℕ} (κ κ' : EdgeColouring k) : Prop :=
  ∃ σ : Equiv.Perm SignType, ∀ e, κ' e = σ (κ e)

/-- The equivalence class of an edge-colouring. -/
def eqClass {k : ℕ} (κ : EdgeColouring k) : Set (EdgeColouring k) :=
  {κ' | Equivalent κ κ'}

/-! ### The classes of (6.4): the circuit of length 5 (0-based: paper's `e_i` is `i - 1`) -/

/-- The edge-colouring of the 5-circuit with value `1` on edge `i`, `-1` on edge `j`, and `0`
elsewhere (used only with `i ≠ j`). -/
def base5 (i j : Fin 5) : EdgeColouring 5 :=
  fun e => if e = i then 1 else if e = j then -1 else 0

/-- `𝒜_ij`: the equivalence class of `base5 i j` (used only with `i ≠ j`). -/
def A (i j : Fin 5) : Set (EdgeColouring 5) := eqClass (base5 i j)

/-- `𝒞_i = 𝒜_ij ∪ 𝒜_ik ∪ 𝒜_jk` where `e_j, e_k` are the two edges with a common end with `e_i`,
namely edges `i - 1` and `i + 1`. -/
def C5 (i : Fin 5) : Set (EdgeColouring 5) :=
  A i (i - 1) ∪ A i (i + 1) ∪ A (i - 1) (i + 1)

/-- `𝒟_i = 𝒜_ac ∪ 𝒜_ad ∪ 𝒜_bc ∪ 𝒜_bd`, where the edges different from `e_i` are
`e_a, e_b, e_c, e_d` in order: `(a, b, c, d) = (i + 1, i + 2, i + 3, i + 4)`. -/
def D5 (i : Fin 5) : Set (EdgeColouring 5) :=
  A (i + 1) (i + 3) ∪ A (i + 1) (i + 4) ∪ A (i + 2) (i + 3) ∪ A (i + 2) (i + 4)

/-- `ℰ = 𝒜₁₂ ∪ 𝒜₂₃ ∪ 𝒜₃₄ ∪ 𝒜₄₅ ∪ 𝒜₁₅` (0-based indices). -/
def E5 : Set (EdgeColouring 5) :=
  A 0 1 ∪ A 1 2 ∪ A 2 3 ∪ A 3 4 ∪ A 0 4

/-! ### The classes of (6.3): the circuit of length 4 -/

/-- `𝒞₀, 𝒞₁, 𝒞₂, 𝒞₃` of (6.3): the edge-colourings equivalent to `(0,0,0,0)`, `(0,1,1,0)`,
`(0,1,0,1)`, `(0,0,1,1)` respectively (listed on `e₁, …, e₄`, i.e. edges `0, …, 3`). -/
def C4 : Fin 4 → Set (EdgeColouring 4)
  | 0 => eqClass ![0, 0, 0, 0]
  | 1 => eqClass ![0, 1, 1, 0]
  | 2 => eqClass ![0, 1, 0, 1]
  | 3 => eqClass ![0, 0, 1, 1]

end FourColourRSST.Ring


