-- Prove2me | Definitions.Def_TransvectionMixing_walkMat
-- name    : TransvectionMixing_walkMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:27.767193+00:00
-- url     : https://prove2.me/theorems/27d3331b-52b7-44b4-986d-bb48567a5cff
-- title:
--   Transvection walk: skeletons and the walk matrix $(I_n+a_tE_{J_t,I_t})\cdots(I_n+a_1E_{J_1,I_1})$
-- statement:
--   A **skeleton** of length $t$ on $n$ rows is a sequence $\sigma=((I_1\mapsto J_1),\dots,(I_t\mapsto J_t))$ of ordered pairs of distinct rows $I_s\neq J_s$; it records the row pairs of a walk (with repetitions) but not its coefficients. The **update** $I\mapsto J$ with coefficient $a$ is left multiplication by the transvection
--   $$
--   I_n + a\,E_{J,I},\qquad E_{J,I}=e_Je_I^\top ,
--   $$
--   which adds $a$ times row $I$ to row $J$. For coefficients $a=(a_1,\dots,a_t)$ in a commutative ring $R$, the **walk matrix** is
--   $$
--   W(\sigma,a)=(I_n+a_tE_{J_t,I_t})\cdots(I_n+a_1E_{J_1,I_1}),
--   $$
--   so step $1$ is applied first and the walk started at $X$ is at $X_t=W(\sigma,a)X$. Concatenation $\sigma\tau$ runs $\sigma$ first. Taking $R=\mathbb F_q[a_1,\dots,a_t]$ and the coefficients to be the indeterminates gives the **coefficient map** as a matrix of polynomials.
--
--   The module also fixes the restriction $M|_{\mathcal S}$ of a matrix to a set $\mathcal S\subseteq[n]\times[n]$ of entries and the uniform probability $\#\{\omega:P(\omega)\}/\#\Omega$ of an event on a finite sample space, which is how every law of the mission is expressed.
--
--   **Formalization Note** Rows are `Fin n`, numbered from $0$. A pair is `{p : Fin n × Fin n // p.1 ≠ p.2}` with `p.1` the source $I$ and `p.2` the target $J$; the step is Mathlib's `Matrix.transvection J I a` (index order reversed). The uniform probability returns $0$ on an empty sample space.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), §1, p.2 (the walk and the skeleton); §3.1, p.9 (the coefficient map); p.4 (concatenation)

import Mathlib

namespace TransvectionMixing

/-- An ordered pair of distinct rows `(I, J)` of an `n × n` matrix, read as the update
`I ↦ J` (source `I = p.1.1`, target `J = p.1.2`) of Braverman–Jain–Newman, *Optimal Marginal
Mixing for Transvection-Based Trapdoored Matrices over Large Fields* (manuscript, sha256
217f833f…), §1, p.2.

**Formalization Note** Rows are `Fin n`, numbered from `0` (the paper's `[n]` is 1-based). -/
abbrev Pair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- A skeleton of length `t`: the list of row pairs `((I₁ ↦ J₁), …, (I_t ↦ J_t))`, `I_s ≠ J_s`,
with repetitions but without coefficients (manuscript sha256 217f833f…, §1, p.2). -/
abbrev Skel (n t : ℕ) : Type := Fin t → Pair n

/-- Concatenation `στ` of two skeletons: `σ` runs first (manuscript sha256 217f833f…, p.4). -/
def Skel.append {n t₁ t₂ : ℕ} (σ : Skel n t₁) (τ : Skel n t₂) : Skel n (t₁ + t₂) :=
  Fin.append σ τ

/-- The elementary matrix of the update `I ↦ J` with coefficient `a`: `Iₙ + a E_{J,I}`, which
adds `a` times row `I` to row `J` under left multiplication (manuscript sha256 217f833f…, §1,
p.2). In Mathlib this is `Matrix.transvection J I a` (note the index order). -/
def stepMat {R : Type*} [CommRing R] {n : ℕ} (p : Pair n) (a : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.transvection p.1.2 p.1.1 a

/-- The product of the elementary matrices of a skeleton with coefficients `a`:
`(Iₙ + a_t E_{J_t,I_t}) ⋯ (Iₙ + a_1 E_{J_1,I_1})`, step `1` applied first (manuscript sha256
217f833f…, §1, p.2 and §3.1, p.9). The walk started at `X` is at `walkMat σ a * X` after
`t` steps.

**Formalization Note** The coefficients live in an arbitrary commutative ring `R`: `R = 𝔽_q`
gives the walk, `R = MvPolynomial (Fin t) 𝔽_q` with `a = X` gives the coefficient map as a
polynomial matrix. The product is the list `[M₁, …, M_t]` reversed, so `M_t` is leftmost. -/
def walkMat {R : Type*} [CommRing R] {n t : ℕ} (σ : Skel n t) (a : Fin t → R) :
    Matrix (Fin n) (Fin n) R :=
  ((List.finRange t).map (fun s => stepMat (σ s) (a s))).reverse.prod

/-- The coefficient map of a skeleton as a matrix of polynomials in the `t` coefficient
indeterminates (manuscript sha256 217f833f…, §3.1, p.9, before projection and before the
initial matrix). -/
noncomputable def coeffPoly {F : Type*} [CommRing F] {n t : ℕ} (σ : Skel n t) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin t) F) :=
  walkMat σ (fun s => MvPolynomial.X s)

/-- The restriction `M|_𝒮` of a matrix to a set `𝒮 ⊆ [n] × [n]` of entries. -/
def restrictEntries {R : Type*} {n : ℕ} (S : Finset (Fin n × Fin n))
    (M : Matrix (Fin n) (Fin n) R) : ↥S → R :=
  fun e => M e.1.1 e.1.2

/-- The uniform probability `#{ω : P ω} / #Ω` of an event on a finite sample space (all laws
of the mission are uniform: skeletons, coefficients, independent tuples of skeletons). Returns
`0` on an empty sample space. -/
noncomputable def prob {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  open Classical in ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

end TransvectionMixing


