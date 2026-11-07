-- Prove2me | Definitions.Def_HZTractability_Market
-- name    : HZTractability_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:12:43.29141+00:00
-- url     : https://prove2.me/theorems/8a25f581-5b63-4568-ba8c-4f567fd76649
-- title:
--   The market $M(G;a,\tau,K)$ (§3, Table 2)
-- statement:
--   Fix a rational $a\in(0,1)$, a parameter $\tau$, a wire size $K$ and a directed graph $G$. The market $M(G;a,\tau,K)$ has unit-supply goods and buyers with budget one who each require one unit. For each vertex $v$ there are five groups of goods and five buyer populations:
--
--   | Good group | Number | | Buyer population | Number | Nonzero utilities |
--   |---|---|---|---|---|---|
--   | $L_v$ (low target) | $S_L$ | | lower links $B^{LM}_v$ | $b_v$ | $a$ on $L_v$; $1$ on $M_v$ |
--   | $M_v$ (middle target) | $S_M$ | | upper buyers $B^{MH}_v$ | $c_v$ | $a$ on $M_v$, $RU_v$; $1$ on $H_v$ |
--   | $H_v$ (high target) | $S_H$ | | floors $F_v$ | $F_v$ | $a$ on $L_v$; $1$ on $M_v$, $RF_v$ |
--   | $RF_v$ (floor reference) | $S^R_{Fv}$ | | floor anchors $AF_v$ | $A^R_{Fv}$ | $1$ on $RF_v$ |
--   | $RU_v$ (upper reference) | $S^R_{Uv}$ | | upper anchors $AU_v$ | $A^R_{Uv}$ | $1$ on $RU_v$ |
--
--   For each edge $u\to v$ there is a population $E_{uv}$ of $K$ wire buyers with utility $a$ on $L_u$ and $1$ on $H_v$; a self-loop is one population approving $L_v$ and $H_v$. Finally, the balancing group $Z$ has $N-G_{\mathrm{listed}}$ goods valued at zero by everyone, where $N$ is the number of buyers and $G_{\mathrm{listed}}$ the number of goods in the five groups at all vertices. Every unlisted utility is zero. The counts depend on the degrees of $v$ through (17), (7), (5).
--
--   This is the market whose approximate equilibria encode threshold-game solutions.
--
--   **Formalization Note** Buyers and goods are structured finite types indexed by vertex, tag and copy, plus wire buyers indexed by edge and copy and the balancing goods; their order is immaterial. Each count is the natural-number ceiling of its rational formula (equal to it by Lemma A.1). The number of balancing goods uses natural subtraction, which is exact by Lemma A.3. Utilities are real numbers in $\{0,a,1\}$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §3, pp.9–11 (PDF pp.11–13), Table 2, p.11; §3.1, p.10; counts §4.4, p.17

import Mathlib
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_bvQ
import Definitions.Def_HZTractability_FvQ
import Definitions.Def_HZTractability_SRFQ

namespace HZTractability

/-- The five groups of goods at a vertex (§3.1, p.9; Table 2, p.11): the targets `L_v`, `M_v`,
`H_v` and the references `RF_v`, `RU_v`. -/
inductive GTag
  | L | M | H | RF | RU
  deriving DecidableEq

instance : Fintype GTag where
  elems := {GTag.L, GTag.M, GTag.H, GTag.RF, GTag.RU}
  complete := by intro x; cases x <;> simp

/-- The five buyer populations at a vertex (§3.1, p.9; Table 2, p.11): lower links `B^{LM}_v`,
upper buyers `B^{MH}_v`, floors `F_v`, floor anchors `AF_v`, upper anchors `AU_v`. -/
inductive BTag
  | BLM | BMH | F | AF | AU
  deriving DecidableEq

instance : Fintype BTag where
  elems := {BTag.BLM, BTag.BMH, BTag.F, BTag.AF, BTag.AU}
  complete := by intro x; cases x <;> simp

/-- The supply of each group at a vertex of outdegree `o` (Table 2, p.11; counts from (17) and (5)):
`S_L`, `S_M`, `S_H`, `S^R_{Fv}`, `S^R_{Uv}`, each the natural number `⌈·⌉₊` of its rational formula
(Lemma A.1 proves each formula is a positive integer, so `⌈·⌉₊` changes nothing). -/
def supCount (a τ : ℚ) (K o : ℕ) : GTag → ℕ
  | .L => ⌈SLQ a K o⌉₊
  | .M => ⌈SMQ a K o⌉₊
  | .H => ⌈SHQ a⌉₊
  | .RF => ⌈SRFQ a τ K o⌉₊
  | .RU => ⌈SRUQ a τ K o⌉₊

/-- The size of each buyer population at a vertex of indegree `h` and outdegree `o` (Table 2,
p.11; counts from (17), (7), (5)): `b_v`, `c_v`, `F_v`, `A^R_{Fv}`, `A^R_{Uv}`, each `⌈·⌉₊` of its
rational formula. -/
def popCount (a τ : ℚ) (K h o : ℕ) : BTag → ℕ
  | .BLM => ⌈bvQ a h⌉₊
  | .BMH => ⌈cvQ a K o⌉₊
  | .F => ⌈FvQ a K o⌉₊
  | .AF => ⌈ARFQ a τ K o⌉₊
  | .AU => ⌈ARUQ a τ K o⌉₊

/-- The buyers of `M(G; a, τ, K)`: for each vertex `v` and population tag `t`, `popCount … t`
individual buyers; and for each edge `u → v`, the `K` wire buyers `E_uv` (§3.1, p.10). -/
abbrev Buyer (a τ : ℚ) (K : ℕ) (G : ThrGraph) : Type :=
  (Σ v : Fin G.n, Σ t : BTag, Fin (popCount a τ K (G.indeg v) (G.outdeg v) t)) ⊕ (G.Edge × Fin K)

/-- `G_listed`, the number of goods in the five groups at all vertices (§3.1, p.10). -/
def Glisted (a τ : ℚ) (K : ℕ) (G : ThrGraph) : ℕ :=
  ∑ v : Fin G.n, ∑ g : GTag, supCount a τ K (G.outdeg v) g

/-- The goods of `M(G; a, τ, K)`: for each vertex `v` and group tag `g`, `supCount … g` unit-supply
goods; and the balancing group `Z` of `N − G_listed` goods, where `N` is the number of buyers
(§3.1, p.10: "Add N − G_listed goods to Z"). -/
abbrev Good (a τ : ℚ) (K : ℕ) (G : ThrGraph) : Type :=
  (Σ v : Fin G.n, Σ g : GTag, Fin (supCount a τ K (G.outdeg v) g)) ⊕
    Fin (Fintype.card (Buyer a τ K G) - Glisted a τ K G)

/-- The utility of a vertex population for a group at the same vertex (Table 2, p.11): lower links
`a` on `L_v`, `1` on `M_v`; upper buyers `a` on `M_v` and `RU_v`, `1` on `H_v`; floors `a` on `L_v`,
`1` on `M_v` and `RF_v`; floor anchors `1` on `RF_v`; upper anchors `1` on `RU_v`; all else `0`. -/
def vutil (a : ℚ) : BTag → GTag → ℚ
  | .BLM, .L => a
  | .BLM, .M => 1
  | .BMH, .M => a
  | .BMH, .RU => a
  | .BMH, .H => 1
  | .F, .L => a
  | .F, .M => 1
  | .F, .RF => 1
  | .AF, .RF => 1
  | .AU, .RU => 1
  | _, _ => 0

/-- **The market `M(G; a, τ, K)`** (Panageas–Shein–Taherijam–Vazirani, *Exploring the
Tractability Frontier of Hylland–Zeckhauser Models*, arXiv:2610.35848, held version, sha256
74b7bf9f…, §3, pp.9–11 (PDF 11–13), Table 2, p.11; counts §4.4, p.17): the utility matrix.

Every good has unit supply and every buyer budget one and demand one unit (§3, p.9). A vertex
population values only groups at its own vertex, as in `vutil`. A wire buyer of the edge `u → v`
values the low group `L_u` at `a` and the high group `H_v` at `1` (a self-loop `v → v` is one
population approving `L_v` and `H_v`). Every other utility is `0`; in particular every buyer values
every balancing good in `Z` at `0`.

**Formalization Note** Buyers and goods are the structured finite types `Buyer`, `Good`; the order
of buyers and goods is immaterial to every statement about the market. Utilities are real numbers in
`{0, a, 1}`. Group sizes are natural numbers (`supCount`, `popCount`); the number of balancing goods
is `N − G_listed` in natural subtraction, which is the true difference by Lemma A.3. -/
noncomputable def mkt (a τ : ℚ) (K : ℕ) (G : ThrGraph) :
    Buyer a τ K G → Good a τ K G → ℝ
  | Sum.inl ⟨v, t, _⟩, Sum.inl ⟨w, g, _⟩ => if v = w then ((vutil a t g : ℚ) : ℝ) else 0
  | Sum.inr ⟨e, _⟩, Sum.inl ⟨w, g, _⟩ =>
      if g = GTag.L ∧ w = e.1.1 then (a : ℝ) else if g = GTag.H ∧ w = e.1.2 then 1 else 0
  | _, Sum.inr _ => 0

/-- The vertex and group of a good (`none` for a balancing good in `Z`). -/
def goodInfo {a τ : ℚ} {K : ℕ} {G : ThrGraph} : Good a τ K G → Option (Fin G.n × GTag)
  | Sum.inl ⟨v, g, _⟩ => some (v, g)
  | Sum.inr _ => none

/-- The vertex and population of a buyer (`none` for a wire buyer). -/
def buyerInfo {a τ : ℚ} {K : ℕ} {G : ThrGraph} : Buyer a τ K G → Option (Fin G.n × BTag)
  | Sum.inl ⟨v, t, _⟩ => some (v, t)
  | Sum.inr _ => none

end HZTractability


