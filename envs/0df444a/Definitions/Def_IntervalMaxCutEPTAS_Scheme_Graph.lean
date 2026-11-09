-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Graph
-- name    : IntervalMaxCutEPTAS_Scheme_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:01.079326+00:00
-- url     : https://prove2.me/theorems/a8d62621-1ba2-42fd-840b-0a6ef4788217
-- title:
--   Interval representations, cuts, Max-Cut and Max-Bisection
-- statement:
--   An **interval representation** of a graph on the vertex set $V=\{0,\dots,n-1\}$ assigns to every vertex $v$ a closed interval $[\ell_v,r_v]$ with $\ell_v\le r_v$; the endpoints lie in a linearly ordered set $R$ (the paper's case is $R=\mathbb R$). Distinct vertices $u,v$ are adjacent exactly when the intervals meet:
--
--   $$u\sim v\iff \max\{\ell_u,\ell_v\}\le\min\{r_u,r_v\}.$$
--
--   The $2n$ endpoints are indexed by left endpoints $\ell_v$ and right endpoints $r_v$. An integer representation $J$ has the **same comparisons** as $I$ if $e\le e'$ holds for two endpoints of $I$ exactly when it holds for the corresponding endpoints of $J$; this is how an algorithm that may only compare endpoints receives real input.
--
--   For a finite simple graph $G$ and $S\subseteq V(G)$, $\mathrm{cut}_G(S)$ is the number of edges with exactly one endpoint in $S$ (each edge counted once), and
--
--   $$\mathrm{mc}(G)=\max_{S}\mathrm{cut}_G(S),\qquad \mathrm{mb}(G)=\max\{\mathrm{cut}_G(S): |S|=\lfloor n/2\rfloor\}.$$
--
--   These are the objects of the paper's main theorem.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §1.1 and §3 (Preliminaries: interval graphs, cut_G, mc, mb), PDF p. 14 (printed p. 13)

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-! # Interval representations, cuts, Max-Cut and Max-Bisection (§1.1, §3) -/

/-- An interval representation of a graph on the vertex set `Fin n`: vertex `v` gets the closed
interval `[l v, r v]` with `l v ≤ r v`, endpoints in a linearly ordered set `R`. -/
structure Rep (R : Type) [LinearOrder R] (n : ℕ) where
  l : Fin n → R
  r : Fin n → R
  le : ∀ v, l v ≤ r v

/-- The graph represented: distinct `u, v` are adjacent iff `max{l u, l v} ≤ min{r u, r v}`. -/
def Rep.graph {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ max (I.l u) (I.l v) ≤ min (I.r u) (I.r v)
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [max_comm, min_comm]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

instance {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) : DecidableRel I.graph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ max (I.l u) (I.l v) ≤ min (I.r u) (I.r v)))

/-- The `2n` endpoints: `inl v ↦ l v` (left endpoint), `inr v ↦ r v` (right endpoint). -/
def Rep.ends {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) : Fin n ⊕ Fin n → R :=
  Sum.elim I.l I.r

/-- `J` (integer endpoints) has exactly the endpoint comparisons of `I`: the program only ever sees
the order of the `2n` endpoints. -/
def SameComparisons {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) (J : Rep ℤ n) : Prop :=
  ∀ a b, I.ends a ≤ I.ends b ↔ J.ends a ≤ J.ends b

section Cuts
variable {V : Type} [Fintype V] [DecidableEq V]

/-- `cut_G(S)`: the number of edges with exactly one endpoint in `S`; each edge is counted once,
as the ordered pair (endpoint in `S`, endpoint outside `S`). -/
def cutCount (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card

/-- `mc(G) = max_S cut_G(S)` over all vertex sets. -/
def mc (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset (Finset V)).sup (cutCount G)

/-- `mb(G)`: the maximum of `cut_G(S)` over all `S` with `|S| = ⌊n/2⌋` (bisections). -/
def mb (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter
    (fun S => S.card = Fintype.card V / 2)).sup (cutCount G)

end Cuts

end IntervalMaxCutEPTAS.Scheme


