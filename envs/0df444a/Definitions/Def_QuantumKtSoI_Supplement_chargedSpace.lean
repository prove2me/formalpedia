-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_chargedSpace
-- name    : QuantumKtSoI_Supplement_chargedSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:30:00.723767+00:00
-- url     : https://prove2.me/theorems/9fdfb290-42ab-449d-8f21-a3280683d202
-- title:
--   Charged space $\mathrm{sp}_A(x,\rho)$ (Definition 7.6)
-- statement:
--   Let $A$ be a native machine with tape alphabets $\Sigma_j$ and state set $Q_A$, tape $1$ being the input tape. For an input $x$ and a branch $\rho$, let $h_j$ be the current head position and $v_j$ the largest position visited so far on tape $j$. The **charged space** is
--   $$\mathrm{sp}_A(x,\rho)=|x|+\sum_{j\ne \mathrm{in}}(v_j+1)\lceil\log(|\Sigma_j|+1)\rceil+\sum_{j}\lceil\log(h_j+2)\rceil+\lceil\log(|Q_A|+2)\rceil .$$
--   The machine **runs in charged space $S$** if $\mathrm{sp}_A(x,\rho)\le S(|x|)$ for every input $x$ of every sufficiently large length and every branch $\rho$, the final ones included.
--
--   This is the space measure of the space-restricted gap lower bound, Theorem 7.8.
--
--   **Formalization Note** A branch is a record sequence $\rho$ with nonzero branch vector; by Lemma 3.3 all configurations in its support share the head positions, so $h_j$ is read from any of them and $v_j$ is the largest head position over the prefixes of $\rho$. Head positions are integers, nonnegative on reachable configurations.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 7.6, p.105

import Mathlib
import Definitions.Def_QuantumKtSoI_Machine_outputProb

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- **Definition 7.6** (Charged space, p.105 of Myrisiotis, STOC 2027 submission, held version
sha256 6616571c…). For a machine `A` with tape alphabets `Σ_j` and state set `Q_A`, an input `x`, a
record sequence `ρ` of length `s` and a configuration `C` in the support of its branch vector `ψ_ρ`,
`sp_A(x, ρ) = |x| + Σ_{j ≠ in} (v_j + 1)⌈log(|Σ_j| + 1)⌉ + Σ_j ⌈log(h_j + 2)⌉ + ⌈log(|Q_A| + 2)⌉`,
where `h_j` is the current head position on tape `j` and `v_j` the largest position visited so far
on tape `j`, i.e. the largest head position on tape `j` over the configurations reached by the
prefixes of `ρ` (of lengths `0, …, s`). The input tape is excluded from the first sum.

**Formalization Note** By Lemma 3.3 all configurations in the support of a nonzero `ψ_ρ` share the
state and the head positions, so taking `h_j` from any `C` in the support and the maximum over the
supports of the prefixes gives the paper's quantity. Head positions are integers; they are
nonnegative for every reachable configuration, and `toNat` is used to read them. -/
def chargedSpace (A : Machine) (x : List Bool) (ρ : List A.Record) (C : A.Config) : ℕ :=
  let v : A.T → ℕ := fun j =>
    (Finset.range (ρ.length + 1)).sup fun i =>
      (A.branch x (ρ.take i)).support.sup fun C' => (C'.head j).toNat
  x.length +
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ A.inT), (v j + 1) * Nat.clog 2 ((A.alph j).card + 1)) +
    (∑ j, Nat.clog 2 ((C.head j).toNat + 2)) + Nat.clog 2 (Fintype.card A.Q + 2)

/-- `A` **runs in charged space** `S` (p.105): `sp_A(x, ρ) ≤ S(|x|)` for every input `x` of every
sufficiently large length and every branch `ρ` (every record sequence with nonzero branch vector),
the final ones included. -/
def RunsInChargedSpace (A : Machine) (S : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length → ∀ s : ℕ, ∀ ρ ∈ A.recSeqs x s,
    ∀ C ∈ (A.branch x ρ).support, (chargedSpace A x ρ C : ℝ) ≤ S x.length

end QuantumKtSoI.Supplement


