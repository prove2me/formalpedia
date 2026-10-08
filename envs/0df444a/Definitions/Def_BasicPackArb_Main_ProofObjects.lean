-- Prove2me | Definitions.Def_BasicPackArb_Main_ProofObjects
-- name    : BasicPackArb_Main_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:58.059916+00:00
-- url     : https://prove2.me/theorems/6b16db1e-c057-414d-966d-56b9f6f74513
-- title:
--   §2: tight sets, domination, good and bad arcs, and the parallel extension $(D-uv, S', \pi', M')$
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots and $M$ a matroid on $S$, with the notation of §1 ($\rho_D$, $S_X=\pi^{-1}(X)$, $r_M$, $\mathrm{Span}_M$). The proof of Theorem 1.6 uses the following notions.
--
--   1. A vertex set $X$ is **tight** if $\rho_D(X)=r_M(S)-r_M(S_X)$. No non-emptiness is required.
--   2. For vertex sets $X$ and $Y$, $Y$ **dominates** $X$ if $S_X\subseteq\mathrm{Span}_M(S_Y)$. A vertex $v$ is identified with $\{v\}$.
--   3. An arc $uv$ is **good** if $v$ dominates $u$, that is $S_u\subseteq\mathrm{Span}_M(S_v)$; otherwise it is **bad**.
--   4. For an arc $a=uv$ and an element $s\in S$: $S'=S\cup\{s'\}$ with a new element $s'$; $M'$ is the matroid on $S'$ obtained from $M$ by adding $s'$ parallel to $s$; and $\pi'$ is the placement of $S'$ that agrees with $\pi$ on $S$ and puts $s'$ at $v$. Together with $D'=D-uv$ this gives the digraph with roots $(D',S',\pi')$ and matroid $M'$ of the induction step.
--
--   These are the auxiliary objects of §2: Claims 2.2–2.4 are about tight sets and domination, and the induction removes a bad arc while adding a parallel root.
--
--   **Formalization Note** Tightness is written additively, $\rho_D(X)+r_M(S_X)=r_M(S)$, in $\mathbb{N}_\infty$; since $r_M(S_X)\le r_M(S)$ this is the paper's equation. $S'$ is `Option S` with $s'$ = `none`, $\pi'$ sends `none` to the head of the arc and `some x` to $\pi(x)$, and $M'$ is Mathlib's `Matroid.comap` of $M$ along $o\mapsto o.\mathrm{getD}\ s$: a set $I\subseteq S'$ is independent in $M'$ iff this map is injective on $I$ and sends it to an independent set of $M$. So $M'$ restricted to $S$ is $M$, $s'$ behaves exactly as $s$, and $\{s,s'\}$ is dependent: $s'$ is parallel to $s$. Its ground set is all of $S'$ whenever $M$'s ground set is all of $S$.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 4 (tight, dominates, good/bad arc, after Claim 2.1) and p. 5 (D′, S′, M′, π′ in the proof of sufficiency in Theorem 1.6)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph

namespace BasicPackArb.Main

/-- `X` is tight (p. 4): `ρ_D(X) = r_M(S) − r_M(S_X)`, written additively as
`ρ_D(X) + r_M(S_X) = r_M(S)` in `ℕ∞`. No non-emptiness is required. -/
def IsTight {V Arc S : Type*} [DecidableEq V] (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (X : Finset V) : Prop :=
  (D.inDeg X : ℕ∞) + M.eRk (π ⁻¹' (X : Set V)) = M.eRk Set.univ

/-- `Y` dominates `X` (p. 4): `S_X ⊆ Span_M(S_Y)`. A vertex `v` is identified with `{v}`. -/
def Dominates {V S : Type*} (π : S → V) (M : Matroid S) (Y X : Finset V) : Prop :=
  π ⁻¹' (X : Set V) ⊆ Span M (π ⁻¹' (Y : Set V))

/-- The arc `a = uv` is good (p. 4) if `v` dominates `u`, i.e. `S_u ⊆ Span_M(S_v)`; otherwise it
is bad. -/
def IsGoodArc {V Arc S : Type*} (D : Digraph V Arc) (π : S → V) (M : Matroid S) (a : Arc) :
    Prop :=
  Dominates π M {D.head a} {D.tail a}

/-- The placement `π'` of `S' = S ∪ {s'}` (p. 5), with `S'` encoded as `Option S` and the new element
`s'` as `none`: `π'` agrees with `π` on `S` and places `s'` at the head `v` of the arc `a = uv`. -/
def extPlacement {V Arc S : Type*} (D : Digraph V Arc) (π : S → V) (a : Arc) :
    Option S → V :=
  fun o => o.elim (D.head a) π

/-- The matroid `M'` on `S' = Option S` (p. 5) obtained from `M` by adding the new element
`s' = none` parallel to `s`: a set `I ⊆ S'` is independent iff `o ↦ o.getD s` is injective on `I`
and maps it onto an independent set of `M`. Hence it restricts to `M` on `S`, and `{s, s'}` is
dependent. -/
def extMatroid {S : Type*} (M : Matroid S) (s : S) : Matroid (Option S) :=
  M.comap (fun o => o.getD s)

end BasicPackArb.Main


