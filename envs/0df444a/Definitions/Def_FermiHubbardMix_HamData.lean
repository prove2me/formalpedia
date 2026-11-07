-- Prove2me | Definitions.Def_FermiHubbardMix_HamData
-- name    : FermiHubbardMix_HamData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:03.250278+00:00
-- url     : https://prove2.me/theorems/d5296ca2-8463-4379-b85e-f188f3e1f27e
-- title:
--   Local fermionic Hamiltonian with onsite terms, coupling strength $\zeta$, bounded couplings, truncation $H^{\mathrm{int}}_\Omega$
-- statement:
--   A **local fermionic Hamiltonian with onsite terms** on $\Lambda$ (Definition 11.7) is a decomposition
--   $$
--   H=V+W,\qquad V=\sum_{i\in\Lambda}v_i,\qquad W=\sum_{Z\subseteq\Lambda,\ |Z|\ge2}w_Z,
--   $$
--   where (1) each $v_i\in\mathfrak A^{\mathrm{ev}}_{\{i\}}$ is Hermitian, (2) each $w_Z\in\mathfrak A^{\mathrm{ev}}_Z$ is Hermitian, and (3) $\operatorname{supp}(w_Z)=Z$ whenever $w_Z\ne0$. The support family is $E_H=\{Z:|Z|\ge2,\ w_Z\ne0\}$.
--
--   The **local multi-site coupling strength** (Definition 4.1) is
--   $$
--   \zeta=\max_{i\in\Lambda}\sum_{Z\in E_H,\ i\in Z}|Z|\,\|w_Z\|.
--   $$
--   For integers $L\ge2$, $D\ge1$, $W$ has **bounded $L$-site degree-$D$ couplings** if $\|w_Z\|\le1$ and $|Z|\le L$ for every $Z\in E_H$, and every site lies in at most $D$ sets of $E_H$. For a region $\Omega\subseteq\Lambda$, the **interaction-truncated Hamiltonian** (Definition 4.4) is $H^{\mathrm{int}}_\Omega=V+\sum_{Z\in E_H,\,Z\subseteq\Omega}w_Z$; it keeps every onsite term.
--
--   These are the Hamiltonians of Part II: onsite terms are arbitrary, and only the multi-site part is constrained.
--
--   **Formalization Note** The data $(v_i)$, $(w_Z)$ are a structure without conditions; Definition 11.7 is the predicate `IsLocal`. Since $\operatorname{supp}(A)=\bigcap\{S:A\in\mathfrak A_S\}$, condition (3) says that every $S$ with $w_Z\in\mathfrak A_S$ contains $Z$. The maximum over sites is a supremum ($0$ for an empty site set). `smul c H` multiplies all terms by $c$.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 11.7, p.52; Definition 4.1, p.15; Definition 4.4, p.16

import Mathlib
import Definitions.Def_FermiHubbardMix_localAlg
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- The data of a fermionic Hamiltonian with onsite terms: onsite terms `v_i` (`i ∈ Λ`) and
multi-site terms `w_Z` (`Z ⊆ Λ`) (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 11.7, p.52). Only the `w_Z` with `|Z| ≥ 2` enter any construction; the conditions of
Definition 11.7 are `HamData.IsLocal`. -/
structure HamData (Λ : Type*) (N : ℕ) where
  /-- the onsite terms `v_i` -/
  v : Λ → Op N
  /-- the multi-site coupling terms `w_Z` -/
  w : Finset Λ → Op N

namespace HamData

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}

/-- The operator `H = V + W = ∑_i v_i + ∑_{|Z| ≥ 2} w_Z` (arXiv:2604.08408, held version sha256
055b8f8f…, Definition 11.7, p.52). -/
def ham (H : HamData Λ N) : Op N :=
  ∑ i, H.v i + ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => 2 ≤ Z.card), H.w Z

/-- **Definition 11.7 (Local fermionic Hamiltonian with onsite terms)** (arXiv:2604.08408, held
version sha256 055b8f8f…, p.52): (1) each `v_i ∈ 𝔄^ev_{{i}}` and `v_i = v_i†`; (2) each `w_Z ∈ 𝔄^ev_Z`
and `w_Z = w_Z†`; (3) `supp(w_Z) = Z` whenever `w_Z ≠ 0` (for `|Z| ≥ 2`).

**Formalization Note** `supp(A) = ⋂ {S : A ∈ 𝔄_S}`; given `w_Z ∈ 𝔄_Z`, `supp(w_Z) = Z` says that every
`S` with `w_Z ∈ 𝔄_S` contains `Z`. `H` is then Hermitian. -/
def IsLocal (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) : Prop :=
  (∀ i, H.v i ∈ localAlg ord {i} ∧ IsEven (H.v i) ∧ (H.v i).IsHermitian) ∧
  (∀ Z : Finset Λ, 2 ≤ Z.card →
    H.w Z ∈ localAlg ord (Z : Set Λ) ∧ IsEven (H.w Z) ∧ (H.w Z).IsHermitian) ∧
  (∀ Z : Finset Λ, 2 ≤ Z.card → H.w Z ≠ 0 →
    ∀ S : Set Λ, H.w Z ∈ localAlg ord S → (Z : Set Λ) ⊆ S)

/-- The support family `E_H = {Z ⊆ Λ : |Z| ≥ 2, w_Z ≠ 0}` (the hyperedges of the interaction
hypergraph) (arXiv:2604.08408, held version sha256 055b8f8f…, Definition 11.7, p.52, and
Definition 4.1, p.15). -/
def edges (H : HamData Λ N) : Set (Finset Λ) := {Z | 2 ≤ Z.card ∧ H.w Z ≠ 0}

open scoped Classical in
/-- The local multi-site coupling strength `ζ = max_i ∑_{Z ∈ E_H, i ∈ Z} |Z| ‖w_Z‖`
(arXiv:2604.08408, held version sha256 055b8f8f…, Definition 4.1, p.15).

**Formalization Note** The maximum over the finite set `Λ` is a supremum over `Λ` (equal to `0` when
`Λ` is empty). -/
def zeta (H : HamData Λ N) : ℝ :=
  ⨆ i : Λ, ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => Z ∈ H.edges ∧ i ∈ Z),
    (Z.card : ℝ) * opNorm (H.w Z)

open scoped Classical in
/-- **Bounded `L`-site degree-`D` couplings** (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 4.1, p.15): for integers `L ≥ 2`, `D ≥ 1`, `‖w_Z‖ ≤ 1` and `|Z| ≤ L` for every hyperedge, and
every site lies in at most `D` hyperedges. -/
def BoundedCouplings (H : HamData Λ N) (L D : ℕ) : Prop :=
  2 ≤ L ∧ 1 ≤ D ∧ (∀ Z ∈ H.edges, opNorm (H.w Z) ≤ 1 ∧ Z.card ≤ L) ∧
    ∀ i : Λ, (Finset.univ.filter (fun Z : Finset Λ => Z ∈ H.edges ∧ i ∈ Z)).card ≤ D

open scoped Classical in
/-- **Definition 4.4 (Interaction truncation)** (arXiv:2604.08408, held version sha256 055b8f8f…,
p.16, eq. (2)): `H^int_Ω = V + ∑_{Z_a ⊆ Ω} h_a`, which keeps every onsite term. -/
def trunc (H : HamData Λ N) (Ω : Set Λ) : Op N :=
  ∑ i, H.v i + ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => 2 ≤ Z.card ∧ (Z : Set Λ) ⊆ Ω), H.w Z

/-- The rescaled data `c·H` (all terms multiplied by the real number `c`), used for
`H̃ = H_FH/(2t_max)` in the proof of Corollary 15.2 (arXiv:2604.08408, held version sha256
055b8f8f…, p.68). -/
def smul (c : ℝ) (H : HamData Λ N) : HamData Λ N :=
  ⟨fun i => (c : ℂ) • H.v i, fun Z => (c : ℂ) • H.w Z⟩

end HamData

end FermiHubbardMix


