-- Prove2me | Definitions.Def_FermiGaussMix_P
-- name    : FermiGaussMix_P
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:36.239384+00:00
-- url     : https://prove2.me/theorems/94edb2d5-7d5a-4f9a-8261-5e4e54bbb2a4
-- title:
--   Majorana monomials $P_R$ and the spans of quadratic and even operators
-- statement:
--   Let $\gamma_1,\dots,\gamma_{2n}$ be Majorana operators on $n$ modes: Hermitian, with $\{\gamma_a,\gamma_b\}=2\delta_{ab}\mathbf 1$. For an even subset $R=\{r_1<\dots<r_{|R|}\}\subseteq[2n]$, the canonical monomial is
--   $$
--   P_R=i^{|R|/2}\gamma_{r_1}\cdots\gamma_{r_{|R|}} .
--   $$
--   It is Hermitian with $P_R^2=\mathbf 1$, and $P_\varnothing=\mathbf 1$. For a set $B$ of labels, the quadratic operators supported in $B$ are the complex span of the $P_R$ with $R\subseteq B$, $|R|=2$; the even operators supported in $B$ are the complex span of the $P_R$ with $R\subseteq B$, $|R|$ even. An operator is even when it is a combination of even monomials.
--
--   These are the basic objects of the mission: the local terms of the Hamiltonian live in these spans.
--
--   **Formalization Note** The Majoranas are the published Jordan–Wigner operators, with 0-based labels. On one mode, $P_{\{0,1\}}=iXY=-Z$.
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (A.1)–(A.2), (A.5)–(A.6), p. 9

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana

open scoped BigOperators
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- The even subsets `R ⊆ [N]`, `N = 2n`, that index the Majorana monomials of eq. (A.2), p.9 (Han, Zhao,
Liu, arXiv:2609.35159v1). -/
def evenSets (n : ℕ) : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun R => Even R.card)

/-- The canonical Hermitian Majorana monomial of eq. (A.2), p.9 (Han, Zhao, Liu, arXiv:2609.35159v1):
`P_R = i^{|R|/2} γ_{r₁} ⋯ γ_{r_{|R|}}` for an even set `R = {r₁ < ⋯ < r_{|R|}}`.

**Formalization Note** The Majoranas `γ_a` are the published Jordan–Wigner operators
`FermiCap.Gaussian.majorana n a`, with 0-based labels `a : Fin (2 * n)`, and `monomial` is their
increasing-order product. Any family with (A.1) on a `2^n`-dimensional space is unitarily equivalent to this
one. The formula is meant for even `R`; every statement of the mission uses it only there. On `n = 1`,
`P {0,1} = i X Y = -Z`. -/
noncomputable def P (n : ℕ) (R : Finset (Fin (2 * n))) : Op n :=
  Complex.I ^ (R.card / 2) • monomial n (fun p => decide (p ∈ R))

/-- Quadratic operators supported in `B`: the complex span of the `P_R` with `R ⊆ B` and `|R| = 2`. This
is "supp H_{0,B} ⊆ B, H_{0,B} quadratic" of eq. (A.5), p.9 (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** There is no scalar term, as in `H₀ = ¼ γᵀK₀γ` with `K₀` antisymmetric (A.4). -/
def quadraticSpan {n : ℕ} (B : Finset (Fin (2 * n))) : Submodule ℂ (Op n) :=
  Submodule.span ℂ (P n '' {R | R ⊆ B ∧ R.card = 2})

/-- Even operators supported in `B`: the complex span of the `P_R` with `R ⊆ B` and `|R|` even. This is
"supp V_B ⊆ B", "Each V_B is even" of eq. (A.6), p.9 (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** The set `R = ∅` is even and `P_∅ = 1`, so a scalar term is allowed. Page 9 only says
that additive constants are omitted since they do not affect `ρ_β`. -/
def evenSpan {n : ℕ} (B : Finset (Fin (2 * n))) : Submodule ℂ (Op n) :=
  Submodule.span ℂ (P n '' {R | R ⊆ B ∧ Even R.card})

/-- An operator is even if it is a complex combination of even Majorana monomials (Lemma B.6, p.20, Han,
Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** This is not `FermiCap.Gaussian.IsEven`, which is a projector condition `Pρ = ρ` for
pure states. -/
def IsEvenOp {n : ℕ} (Y : Op n) : Prop := Y ∈ evenSpan (Finset.univ : Finset (Fin (2 * n)))

end FermiGaussMix


