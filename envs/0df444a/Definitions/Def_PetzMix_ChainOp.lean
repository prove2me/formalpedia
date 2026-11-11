-- Prove2me | Definitions.Def_PetzMix_ChainOp
-- name    : PetzMix_ChainOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:56.717779+00:00
-- url     : https://prove2.me/theorems/a4b264e9-a39f-4877-9e1a-4d06ea2c9ccc
-- title:
--   The periodic qudit chain: operators, bonds, cyclic distance, blocks and boundaries
-- statement:
--   The system is the periodic chain $\Lambda_n=\mathbb Z/n\mathbb Z$ of $n$ qudits, each with Hilbert space $\mathbb C^d$. Operators on $(\mathbb C^d)^{\otimes n}$ are complex matrices indexed by configurations $\Lambda_n\to\{0,\dots,d-1\}$. An operator on a region $S$ is identified with $A\otimes I_{S^c}$; "$A\in\mathcal A_S$" means that $A$ acts trivially outside $S$.
--
--   This file fixes the geometry of the chain.
--
--   1. Site addition is modulo $n$; the **bond** $\{i,i+1\}$ joins neighbouring sites, and there are $n$ bonds, including $\{n-1,0\}$.
--   2. The **interaction family** of (1): bonds $h^{(i)}_{i,i+1}$, $i\in\Lambda_n$, each a Hermitian operator acting on $\{i,i+1\}$. The Hamiltonian is $H=\sum_i h^{(i)}_{i,i+1}$; neither commutativity nor translation invariance is assumed. (The bound $\|h^{(i)}\|\le1$ is stated separately in each theorem.)
--   3. The **cyclic distance** $\operatorname{dist}(i,j)=\min\{(j-i)\bmod n,(i-j)\bmod n\}$, the distance $\operatorname{dist}(i,B)=\min_{j\in B}\operatorname{dist}(i,j)$, and the neighbourhood $N_r(S)=\{i:\operatorname{dist}(i,S)\le r\}$.
--   4. The **cyclic block** $\{a,a+1,\dots,a+\ell-1\}$ of length $\ell$ with left end $a$. For $1\le\ell<n$ the $n$ blocks of length $\ell$ form the family $\mathcal B_{n,\ell}$; a block $B=[a,b]\subsetneq\Lambda_n$ of §4–§5 is one of them. Consecutive sub-intervals $\{a+p,\dots,a+q-1\}$ of a block describe its decompositions.
--   5. The **boundary** $\partial B$: the sites on the edges that separate $B$ from $B^c$, i.e. $\{a-1,a,b,b+1\}$ for $B=[a,b]$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Sites are `Fin n`; operators are the public `QDSGibbs.Op` with constant local dimension. The bonds are read as Hermitian ((1) calls $H$ a Hamiltonian). `setDist i ∅ = 0` is a junk value never used: distances are only taken to blocks, which are nonempty.
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), §1.1, (1), p.4; Notation, p.12; §3, p.16; §4, p.19; §5 Setup, p.28

import Mathlib
import Definitions.Def_QDSGibbs_Op

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- Operators on the periodic chain `Λn = ℤ/nℤ` of `n` qudits of local dimension `d`, i.e. on
`(ℂ^d)^{⊗n}` (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190
(held copy sha256 38ff48d0…), §1.1, (1), p.4; Notation, p.12).

**Formalization Note** Sites are `Fin n` (paper site `i` is index `i`, both read modulo `n`).
Operators are the public `QDSGibbs.Op` with constant local dimension: matrices indexed by
configurations `Fin n → Fin d`. An operator on a region `S` is represented on the full chain as
`A ⊗ I_{S^c}`; "`A ∈ A_S`" is `QDSGibbs.SupportedOn S A`. -/
abbrev ChainOp (n d : ℕ) : Type := QDSGibbs.Op (fun _ : Fin n => d)

/-- The site `i + k` of the periodic chain, the addition taken modulo `n` ("site indices are
understood modulo n", arXiv:2610.01190, (1), p.4). `cyc i (n - 1)` is the site `i - 1`. -/
def cyc {n : ℕ} (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ i.pos⟩

/-- The bond `{i, i+1}` (modulo `n`) of the periodic chain, the support of the two-site interaction
`h^{(i)}_{i,i+1}` (arXiv:2610.01190, (1), p.4). There are `n` bonds, including `{n-1, 0}`. -/
def bond {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  {i, cyc i 1}

/-- The interaction family of (1) (arXiv:2610.01190, §1.1, (1), p.4): for every site `i` of the
periodic chain, `h i` is a Hermitian two-site interaction supported on the bond `{i, i+1}` (modulo
`n`). The Hamiltonian is `H = Σ_i h i`. Neither commutativity nor translation invariance is assumed.

**Formalization Note** (1) does not say "Hermitian", but `H` is a Hamiltonian and `σ_β` is a state
only for Hermitian `H`; the bonds are read as Hermitian. The norm bound `‖h i‖ ≤ 1` of (1) is stated
separately in every theorem (`QDSGibbs.opNorm (h i) ≤ 1`). -/
def IsPeriodicNN {n d : ℕ} (h : Fin n → ChainOp n d) : Prop :=
  ∀ i, (h i).IsHermitian ∧ SupportedOn (bond i) (h i)

/-- The graph distance of the cycle `ℤ/nℤ` (arXiv:2610.01190, Notation, p.12):
`dist(i, j) = min((j − i) mod n, (i − j) mod n)`. -/
def cycDist {n : ℕ} (i j : Fin n) : ℕ :=
  min ((j.val + n - i.val) % n) ((i.val + n - j.val) % n)

/-- The distance `dist(i, B) = min_{j ∈ B} dist(i, j)` from a site to a set of sites
(arXiv:2610.01190, Notation, p.12).

**Formalization Note** The minimum is `sInf` in `ℕ`; for the empty set the value is `0`. It is only
used for blocks, which are nonempty. -/
noncomputable def setDist {n : ℕ} (i : Fin n) (B : Finset (Fin n)) : ℕ :=
  sInf (cycDist i '' (B : Set (Fin n)))

/-- The radius-`r` neighbourhood `N_r(S) = {i ∈ Λn : dist(i, S) ≤ r}` (arXiv:2610.01190,
Notation, p.12), with the graph distance of the cycle. For large `r` it is the whole chain. -/
def nbhd {n : ℕ} (r : ℕ) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ j ∈ S, cycDist i j ≤ r)

/-- The cyclic interval `{a + p, a + p + 1, …, a + q − 1}` (modulo `n`) of the sites at offsets
`p ≤ k < q` from `a`. It is empty when `q ≤ p`. Used for the consecutive intervals into which a block
is decomposed (arXiv:2610.01190, Assumption 4.4, (61), p.20; Corollary 5.6, p.31). -/
def seg {n : ℕ} (a : Fin n) (p q : ℕ) : Finset (Fin n) :=
  (Finset.Ico p q).image (cyc a)

/-- The cyclic block `{a, a+1, …, a+ℓ−1}` (modulo `n`) of length `ℓ` with left end `a`
(arXiv:2610.01190, Notation, p.12: `B_{n,ℓ}` is the family of all cyclic intervals of length `ℓ`).
For `1 ≤ ℓ < n` the `n` blocks `cycBlock ℓ a`, `a : Fin n`, are distinct and are the family
`B_{n,ℓ}` ("1 ≤ ℓ < n, so that B_{n,ℓ} consists of n cyclic intervals", p.16). A block
`B = [a, b] ⊊ Λn` of §4–§5 (p.19, p.28) is `cycBlock ℓ a` with `1 ≤ ℓ < n`, `b = a + ℓ − 1`. -/
def cycBlock {n : ℕ} (ℓ : ℕ) (a : Fin n) : Finset (Fin n) :=
  seg a 0 ℓ

/-- The boundary `∂B`: the sites adjacent on the edges separating `B` from `B^c`
(arXiv:2610.01190, §4, p.19: "We denote by ∂B the set of sites adjacent on the two edges separating
B from B^c"). A site `i` belongs to `∂B` when one of the edges `{i, i+1}`, `{i−1, i}` has exactly one
endpoint in `B`.

**Formalization Note** For a block `B = [a, b] ⊊ Λn` this is `{a−1, a, b, b+1}` (modulo `n`); it is
consistent with "∂B ⊆ N_1(B)" (p.27). -/
def bdry {n : ℕ} (B : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i ∈ B ↔ cyc i 1 ∉ B) ∨ (cyc i (n - 1) ∈ B ↔ i ∉ B))

end PetzMix


