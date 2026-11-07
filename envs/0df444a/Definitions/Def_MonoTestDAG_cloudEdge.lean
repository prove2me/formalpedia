-- Prove2me | Definitions.Def_MonoTestDAG_cloudEdge
-- name    : MonoTestDAG_cloudEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:54.68714+00:00
-- url     : https://prove2.me/theorems/94d8516d-1119-4072-a693-517c91fdee67
-- title:
--   Definition 5.7: the cloud lift $\mathrm{Cl}_D(U)$
-- statement:
--   For a bipartite $U=(L,R;E)$ and an integer $D\ge1$, the **$D$-cloud lift** $\mathrm{Cl}_D(U)$ is the four-layer DAG on $L^-\cup L\cup R\cup R^+$, where $L^-:=\{(u,a):u\in L,a\in[D]\}$ and $R^+:=\{(v,a):v\in R,a\in[D]\}$. Its edges are $(u,a)\to u$, $u\to v$ for $(u,v)\in E$, and $v\to(v,a)$.
--
--   **Formalization Note.** $[D]$ is indexed by `Fin D`. The condition $D\ge1$ is a hypothesis of the statements using the lift. The module also defines the vertex type `CloudV`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Definition 5.7, p.31

import Mathlib

namespace MonoTestDAG

/-- The vertex set `L⁻ ∪ L ∪ R ∪ R⁺` of the `D`-cloud lift, with `L⁻ = L × [D]` and `R⁺ = R × [D]`.
Constructors: `inl (u, a)` is `(u, a) ∈ L⁻`; `inr (inl (inl u))` is `u ∈ L`;
`inr (inl (inr v))` is `v ∈ R`; `inr (inr (v, a))` is `(v, a) ∈ R⁺`. -/
abbrev CloudV (L R : Type) (D : ℕ) : Type :=
  (L × Fin D) ⊕ (L ⊕ R) ⊕ (R × Fin D)

/-- **Definition 5.7 (cloud lift).** For a bipartite `U = (L, R; E)` and an integer `D ≥ 1`, the
`D`-cloud lift `Cl_D(U)` is the four-layer DAG on `L⁻ ∪ L ∪ R ∪ R⁺`,
`L⁻ := {(u, a) : u ∈ L, a ∈ [D]}`, `R⁺ := {(v, a) : v ∈ R, a ∈ [D]}`, with edges
`(u, a) → u`, `u → v` for `(u, v) ∈ E`, and `v → (v, a)`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Definition 5.7, p.31.

**Formalization Note.** `[D] = {1, …, D}` is indexed by `Fin D`. The condition `D ≥ 1` is a
hypothesis of the statements that use the lift. -/
def cloudEdge {L R : Type} (EU : Finset (L × R)) (D : ℕ) : CloudV L R D → CloudV L R D → Prop
  | .inl (u, _), .inr (.inl (.inl u')) => u = u'
  | .inr (.inl (.inl u)), .inr (.inl (.inr v)) => (u, v) ∈ EU
  | .inr (.inl (.inr v)), .inr (.inr (v', _)) => v = v'
  | _, _ => False

end MonoTestDAG


