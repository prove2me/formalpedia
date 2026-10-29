-- Prove2me | Definitions.Def_ZhangTangLabelCut_LP2_Shutter
-- name    : ZhangTangLabelCut_LP2_Shutter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:12:45.683986+00:00
-- url     : https://prove2.me/theorems/134303eb-d7d0-441b-9533-cbb1a7e05426
-- title:
--   The concrete shutter graph and uniform permutation experiment
-- statement:
--   For integers $k,d,h$, take $\Phi=\{0,\ldots,k-1\}$ and $[d]=\{0,\ldots,d-1\}$. A chain index is a pair $\mu<\nu$ in $\Phi$ together with $i\in\{0,\ldots,h-1\}$. A sample independently chooses a uniform permutation $\sigma^i_{\mu\nu}$ of $[d]$ for each chain.
--
--   Each chain has $d$ diamonds in series. A diamond has two fresh route vertices and four edges: two top edges both labelled $(\mu,j)$ and two bottom edges both labelled $(\nu,\sigma^i_{\mu\nu}(j))$. All chains share their initial terminal $s$ and final terminal $t$; every internal junction and route vertex belongs to its own chain. The orientation flag either allows both traversal directions or directs each edge from the preceding junction toward the following junction. Labels range over $\Phi\times[d]$.
--
--   For an event $A$ the probability is the exact finite counting ratio
--   $$\mathbb P(A)=\frac{|A|}{(d!)^{h\binom{k}{2}}}.$$
--   The implementation counts all functions from the chain set to the permutation group, so it is the uniform product law, not a law on arbitrary maps. For $d,h>0$ and $k\ge2$, the graph has $4dh\binom{k}{2}$ edges and $2+(3d-1)h\binom{k}{2}$ vertices. Definitions are total at zero parameters, but the construction theorems use the positive regime.
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), pp. 8–12, Section 4, Figures 1–3 and equations (3)–(5)

import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut

namespace ZhangTangLabelCut.LP2

abbrev Pair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}
abbrev Chain (k h : ℕ) := Pair k × Fin h
abbrev ShutterVertex (k d h : ℕ) :=
  Bool ⊕ (Chain k h × (Fin (d - 1) ⊕ (Fin d × Bool)))
abbrev ShutterEdge (k d h : ℕ) := Chain k h × (Fin d × Bool × Bool)
abbrev Sample (k d h : ℕ) := Chain k h → Equiv.Perm (Fin d)

/-- End junctions are shared globally; only internal junctions are chain-specific. -/
def junction {k d h : ℕ} (c : Chain k h) (j : Fin (d + 1)) : ShutterVertex k d h :=
  if h0 : j.val = 0 then Sum.inl false
  else if hd : j.val = d then Sum.inl true
  else Sum.inr (c, Sum.inl ⟨j.val - 1, by omega⟩)

def middle {k d h : ℕ} (c : Chain k h) (j : Fin d) (b : Bool) : ShutterVertex k d h :=
  Sum.inr (c, Sum.inr (j, b))

def shutterTail {k d h : ℕ} (e : ShutterEdge k d h) : ShutterVertex k d h :=
  if e.2.2.2 then middle e.1 e.2.1 e.2.2.1 else junction e.1 e.2.1.castSucc

def shutterHead {k d h : ℕ} (e : ShutterEdge k d h) : ShutterVertex k d h :=
  if e.2.2.2 then junction e.1 e.2.1.succ else middle e.1 e.2.1 e.2.2.1

/-- The four edges in each diamond are separate named edges with two fresh route vertices. -/
def shutterGraph (k d h : ℕ) (directed : Bool) : FiniteGraph where
  V := ShutterVertex k d h
  E := ShutterEdge k d h
  finiteV := inferInstance
  finiteE := inferInstance
  tail := shutterTail
  head := shutterHead
  directed := directed

/-- A concrete Section 4 instance, determined only by its independent permutations. -/
def shutterInstance (k d h : ℕ) (directed : Bool) (σ : Sample k d h) : LabelCut where
  graph := shutterGraph k d h directed
  L := Fin k × Fin d
  finiteL := inferInstance
  label := fun e => if e.2.2.1 then (e.1.1.val.2, σ e.1 e.2.1)
                   else (e.1.1.val.1, e.2.1)
  s := Sum.inl false
  t := Sum.inl true
  distinct := by
    change (Sum.inl false : ShutterVertex k d h) ≠ Sum.inl true
    simp

/-- Uniform counting probability on the full product of permutation groups. -/
noncomputable def probability (k d h : ℕ) (event : Sample k d h → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card (Sample k d h)

end ZhangTangLabelCut.LP2


