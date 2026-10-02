-- Prove2me | Definitions.Def_TeschlODE_LocalBehavior_spectralSubspace
-- name    : TeschlODE_LocalBehavior_spectralSubspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:00:31.928856+00:00
-- url     : https://prove2.me/theorems/bfd91f62-0205-4cd0-8913-0602e79fd0c9
-- title:
--   Real span of the generalized eigenvectors for eigenvalues in a set $S$ — the subspaces $E_\pm$ of (9.2)
-- statement:
--   Let $A$ be a real $n \times n$ matrix with eigenvalues $\alpha_j$ of algebraic multiplicities $a_j$, and let $S \subseteq \mathbb{C}$. The **spectral subspace** of $A$ for $S$ is the set of real vectors $x \in \mathbb{R}^n$ which, regarded as vectors of $\mathbb{C}^n$, lie in the sum of the generalized eigenspaces of $A$ for the eigenvalues in $S$:
--   $$E_S(A) = \Big\{ x \in \mathbb{R}^n : x \in \bigoplus_{\alpha_j \in S} \operatorname{Ker}(A - \alpha_j)^{a_j} \Big\}.$$
--
--   With $S = \{\operatorname{Re} z < 0\}$ and $S = \{\operatorname{Re} z > 0\}$ this is the book's (9.2): the linear **stable subspace** $E^+(e^A)$ and **unstable subspace** $E^-(e^A)$ of the flow $e^{tA}$. With $S = \{|z| < 1\}$ and $S = \{|z| > 1\}$ it is the contracting subspace $E^+(A)$ and the expanding subspace $E^-(A)$ of the map $x \mapsto Ax$ (§9.3, p. 262; §10.4). Note the sign convention: $+$ is always the *stable* (contracting) side.
--
--   **Formalization Note.** The generalized eigenspace $\operatorname{Ker}(A - \alpha_j)^{a_j}$ is Mathlib's `Module.End.maxGenEigenspace` of the complexified matrix, the sum is the supremum of submodules, and the real subspace is its preimage under the coordinatewise inclusion $\mathbb{R}^n \to \mathbb{C}^n$. The state space is `Fin n → ℝ`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 253, §9.1, Eq. (9.2); p. 262, §9.3 (E±(A) for maps)

import Mathlib

namespace TeschlODE.LocalBehavior

/-- Teschl, §9.1, Eq. (9.2), p. 253 (and §9.3, p. 262, §10.4, p. 288, for maps): the real
subspace of `ℝⁿ` spanned by the generalized eigenvectors of the real matrix `A` belonging to
eigenvalues in a set `S ⊆ ℂ`. It is the set of real vectors `x` which, regarded as vectors of
`ℂⁿ`, lie in `⨁_{α_j ∈ S} Ker (A − α_j)^{a_j}` (the sum of the maximal generalized eigenspaces
of the complexified matrix). With `S = {z | Re z < 0}` (resp. `{z | Re z > 0}`) this is the
linear stable (resp. unstable) subspace `E₊(e^A)` (resp. `E₋(e^A)`) of the flow `e^{tA}`; with
`S = {z | |z| < 1}` (resp. `{z | |z| > 1}`) it is the contracting (resp. expanding) subspace
`E₊(A)` (resp. `E₋(A)`) of the map `x ↦ Ax`. -/
noncomputable def spectralSubspace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Set ℂ) :
    Submodule ℝ (Fin n → ℝ) :=
  ((⨆ μ ∈ S, Module.End.maxGenEigenspace (Matrix.toLin' (A.map (fun r : ℝ => (r : ℂ)))) μ).restrictScalars
      ℝ).comap
    (LinearMap.pi fun i => Complex.ofRealCLM.toLinearMap ∘ₗ LinearMap.proj i)

end TeschlODE.LocalBehavior


