-- Prove2me | Definitions.Def_SimplicialIso_Mixing_DeltaForms
-- name    : SimplicialIso_Mixing_DeltaForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:22.814351+00:00
-- url     : https://prove2.me/theorems/b17f7301-51de-4cf9-a3b4-a78929efccd4
-- title:
--   §4.3, p. 17 — the forms δ_{A_0,…,A_{d−1}} ∈ Ω^{d−1}, φ = δ_{A_0,A_1,…,A_{d−1}} and ψ = δ_{A_d,A_1,…,A_{d−1}}
-- statement:
--   Let $B_0,\dots,B_{d-1}$ be sets of vertices. The $(d-1)$-form $\delta_{B_0,\dots,B_{d-1}}\in\Omega^{d-1}$ is defined on an oriented $(d-1)$-cell $\sigma=[\sigma_0<\dots<\sigma_{d-1}]$ by
--   $$\delta_{B_0,\dots,B_{d-1}}(\sigma)=\begin{cases}\operatorname{sgn}(\pi) & \exists\,\pi\in\operatorname{Sym}_{\{0,\dots,d-1\}}\text{ with }\sigma_i\in B_{\pi(i)}\text{ for }0\le i\le d-1,\\ 0 & \text{else.}\end{cases}$$
--   For disjoint vertex sets $A_0,\dots,A_d$ the proof of the Mixing Lemma uses
--   $$\varphi=\delta_{A_0,A_1,\dots,A_{d-1}},\qquad \psi=\delta_{A_d,A_1,\dots,A_{d-1}},$$
--   so $\psi$ is obtained from $\varphi$ by replacing the first block $A_0$ by $A_d$, keeping the order of the other blocks.
--
--   These two test forms turn the count $|F(A_0,\dots,A_d)|$ into the bilinear quantity $\langle\varphi,(D-\Delta^+)\psi\rangle$.
--
--   **Formalization Note.** The sign is computed without choosing $\pi$: $\delta(\sigma)$ is nonzero when $\sigma$ has exactly one vertex in each $B_i$ (for disjoint blocks this is the existence of $\pi$), and then equals $(-1)^N$, where $N$ counts the pairs $v<w$ of vertices of $\sigma$ with $v\in B_i$, $w\in B_j$, $j<i$: this is the number of inversions of $\pi$, so $(-1)^N=\operatorname{sgn}\pi$.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 17, definition of δ_{A_0,…,A_{d−1}} (display before (4.5)) and of φ, ψ

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset

variable {n d : ℕ}

/-- The number of inversions of `σ` relative to the blocks `B_0, …, B_{d-1}`: pairs of
vertices `v < w` of `σ` with `v ∈ B_i`, `w ∈ B_j` and `j < i`. When `σ = [σ_0 < ⋯ < σ_{d-1}]`
has one vertex in each block and `π(j)` is the block of `σ_j`, this is the number of
inversions of `π`, so `(-1)^{invCount} = sgn π`. -/
def invCount (B : Fin d → Finset (Fin n)) (σ : Finset (Fin n)) : ℕ :=
  ∑ i, ∑ j ∈ univ.filter (· < i),
    (((σ ∩ B i) ×ˢ (σ ∩ B j)).filter (fun p => p.1 < p.2)).card

/-- The form `δ_{B_0, …, B_{d-1}} ∈ Ω^{d-1}` of §4.3: `δ(σ) = sgn π` if `σ_j ∈ B_{π(j)}` for a
permutation `π` of `{0, …, d-1}`, i.e. if `σ` has exactly one vertex in each block, and
`δ(σ) = 0` otherwise. -/
def delta (B : Fin d → Finset (Fin n)) : Form n d :=
  WithLp.toLp 2 (fun σ =>
    if ∀ i, (σ.1 ∩ B i).card = 1 then (-1 : ℝ) ^ invCount B σ.1 else 0)

/-- `φ = δ_{A_0, A_1, …, A_{d-1}}`. -/
def phi (A : Fin (d + 1) → Finset (Fin n)) : Form n d :=
  delta (fun i : Fin d => A i.castSucc)

/-- `ψ = δ_{A_d, A_1, …, A_{d-1}}`: the family of `φ` with its first block `A_0` replaced by
`A_d`, the other blocks kept in order. -/
def psi (A : Fin (d + 1) → Finset (Fin n)) : Form n d :=
  delta (fun i : Fin d => if (i : ℕ) = 0 then A (Fin.last d) else A i.castSucc)

end SimplicialIso.Mixing


