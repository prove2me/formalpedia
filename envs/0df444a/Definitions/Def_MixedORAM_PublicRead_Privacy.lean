-- Prove2me | Definitions.Def_MixedORAM_PublicRead_Privacy
-- name    : MixedORAM_PublicRead_Privacy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:46:20.851093+00:00
-- url     : https://prove2.me/theorems/d65e0462-1257-40f8-b287-26c980ea5795
-- title:
--   Leakage, comparable inputs, total variation and statistical trace privacy
-- statement:
--   The **hidden-kind leakage** of a request list is its mode sequence together with every complete public request (kind, address, written word). The **disclosed-kind leakage** also contains the kind (read or write) of every private request. Two request lists are **comparable** under a leakage if their leakages are equal (so they have equal length); two inputs are comparable if moreover their initial arrays agree.
--
--   The **total variation distance** of two laws $P,Q$ is $\sup_S\,(P(S)-Q(S))$ over all sets $S$ of outcomes.
--
--   An implementation has **statistical trace privacy on horizon $\bar N$ with distance $\delta$** under a leakage if for every initial array $A_0$ and every two comparable request lists $u,u'$ of length at most $\bar N$,
--   $$d_{\mathrm{TV}}\big(\mathrm{Tr}(A_0,u),\ \mathrm{Tr}(A_0,u')\big)\ \le\ \delta ,$$
--   where $\mathrm{Tr}(A_0,u)$ is the law of the observed trace. The paper's notion is $\delta=1/16$; Theorem 3.1 uses horizon $N+2$.
--
--   **Formalization Note** The supremum over sets is taken in $[0,\infty]$ with truncated subtraction; replacing $S$ by its complement shows it equals $\max_S|P(S)-Q(S)|$. The common initial array is expressed by running both lists from the same $A_0$.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), pp. 4–5, §2.2; p. 75, Appendix G

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_Model

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-- The two leakage functions of §2.2 (p. 4): `hid` (hidden private kinds) and `dis` (disclosed
private kinds). -/
inductive LeakKind where
  | hid
  | dis
  deriving DecidableEq

/-- Hidden-kind leakage of one request: a public request leaks completely (kind, address, write
value), a private one leaks only that it is private. Mapped over a request list, this is the mode
sequence together with every complete public request (§2.2, p. 4: "The leakage Leak_hid of an input
request sequence is its mode sequence together with every complete public request, including
addresses and write values"). -/
def leakHid {n w : ℕ} (r : Request n w) : Option (Op n w) :=
  match r.mode with
  | .pub => some r.op
  | .priv => none

/-- Disclosed-kind leakage of one request: as `leakHid`, and additionally the kind (read/write) of a
private request (§2.2, p. 4: "Leak_dis additionally contains each private request's kind"). -/
def leakDis {n w : ℕ} (r : Request n w) : Op n w ⊕ Kind :=
  match r.mode with
  | .pub => .inl r.op
  | .priv => .inr r.op.kind

/-- Two request lists are **comparable** under the leakage `k` if their leakages agree (§2.2, p. 4:
"Two inputs are comparable if their leakage and initial arrays agree"). Equal leakage forces equal
length. The agreement of the initial arrays is expressed where the notion is used, by running both
lists from the same initial array. -/
def Comparable {n w : ℕ} : LeakKind → List (Request n w) → List (Request n w) → Prop
  | .hid, u, u' => u.map leakHid = u'.map leakHid
  | .dis, u, u' => u.map leakDis = u'.map leakDis

/-- The **total variation distance** of two laws: `sup_S (P(S) − Q(S))` over all sets `S`
(truncated subtraction in `ℝ≥0∞`; the supremum equals `max_S |P(S) − Q(S)|` because `S` may be
replaced by its complement). -/
noncomputable def tvDist {α : Type} (P Q : PMF α) : ENNReal :=
  ⨆ S : Set α, (P.toOuterMeasure S - Q.toOuterMeasure S)

/-- **Statistical trace privacy on horizon `N̄` with distance `δ`** under the leakage `k`: for
every initial array and every two comparable request lists of length at most `N̄`, the laws of the
observed traces are within total variation distance `δ` (§2.2, p. 5 and Appendix G, p. 75:
"Statistical trace privacy on horizon N̄ requires the traces of comparable inputs of length at most
N̄ to be within total variation distance 1/16"; the paper's notion is `δ = 1/16`, and Lemma A.3
speaks of "statistical privacy with distance δ"). -/
def StatPrivate {n w m a : ℕ} (k : LeakKind) (I : Impl n w m a) (Nbar : ℕ) (δ : ENNReal) :
    Prop :=
  ∀ (A₀ : Fin n → BitVec w) (u u' : List (Request n w)), Comparable k u u' →
    u.length ≤ Nbar → tvDist (I.traceDist A₀ u) (I.traceDist A₀ u') ≤ δ

end MixedORAM.PublicRead


