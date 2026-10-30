-- Prove2me | Definitions.Def_SpecExtremalConj_IsTuranPlusConst
-- name    : SpecExtremalConj_IsTuranPlusConst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:36.379205+00:00
-- url     : https://prove2.me/theorems/ddbc7770-c134-4ef8-9ec9-ad940d37f77f
-- title:
--   §3 setting: $\mathrm{Ex}(n,F)$ is $T_{n,r}$ plus exactly $a$ edges
-- statement:
--   Let $F$ be a graph and $r,a,n_1$ natural numbers. **The graphs in $\mathrm{Ex}(n,F)$ are obtained from $T_{n,r}$ by adding $a$ edges** (for $n\ge n_1$) if for every $n\ge n_1$, every $H\in\mathrm{Ex}(n,F)$ contains a (relabelled) spanning copy of $T_{n,r}$ and
--
--   $$e(H)=e(T_{n,r})+a.$$
--
--   In particular $\mathrm{ex}(n,F)=e(T_{n,r})+a$ for $n\ge n_1$ (when $\mathrm{Ex}(n,F)$ is nonempty).
--
--   This is the standing assumption of Section 3, under which all lemmas of the proof of Theorem 1.2 are stated.
--
--   **Formalization Note** "$n$ large enough" is the threshold $n_1$. Membership in $\mathrm{Ex}(n,F)$ is Mathlib's `H.IsExtremal F.Free` on `Fin n`.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §3, p. 4 (unnumbered: "We may assume that the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges. Then ex(n, F) = e(T_{n,r}) + a")

import Mathlib
import Definitions.Def_SpecExtremalConj_ContainsSpanningTuran
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **The §3 setting: Ex(n, F) is T_{n,r} plus exactly a edges.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §3, p. 4 (unnumbered):
"We may assume that the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges. Then
ex(n, F) = e(T_{n,r}) + a".

`IsTuranPlusConst F r a n₁` says: for every `n ≥ n₁`, every extremal `F`-free graph `H` on `Fin n`
contains a spanning copy of `turanGraph n r` and has exactly `e(T_{n,r}) + a` edges.

**Formalization Note.** The paper's "n large enough" is the threshold `n₁`. This is the standing
hypothesis of the lemmas of §3; the mission's goal assumes only `IsTuranPlusO1`, and the reduction
from one to the other is a milestone. -/
def IsTuranPlusConst {W : Type*} (F : SimpleGraph W) (r a n₁ : ℕ) : Prop :=
  ∀ n ≥ n₁, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H.IsExtremal F.Free →
    ContainsSpanningTuran r H ∧ #H.edgeFinset = #(turanGraph n r).edgeFinset + a

end SpecExtremalConj


