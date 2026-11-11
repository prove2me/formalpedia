-- Prove2me | Definitions.Def_QNoiseStab_projLowDeg
-- name    : QNoiseStab_projLowDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:53.227067+00:00
-- url     : https://prove2.me/theorems/b7c1bcfd-b11f-4d4f-8c79-24cddd5830fa
-- title:
--   Projection $\Pi_{B_t}$ onto the states of Fourier degree at most $t$
-- statement:
--   Let $B_t\subseteq\mathbb C^{\mathbb Z_m^n}$ be the subspace spanned by the Fourier basis states $|\hat z\rangle$ with at most $t$ nonzero coordinates; its elements have **Fourier degree at most $t$**. The projection onto $B_t$ is
--
--   $$
--   \Pi_{B_t}=\sum_{z:\ |\mathrm{Supp}'(z)|\le t}|\hat z\rangle\langle\hat z| .
--   $$
--
--   After $t$ queries, the input register of a query algorithm on a uniform input lies in $B_t$ (Corollary 2.9); Lemma 3.3 compares $\Pi_{B_t}$ with the noise operator.
--
--   **Formalization Note** Defined by the sum over Fourier states (p.11), with the primitive root $e^{2\pi i/m}$; because the $|\hat z\rangle$ are orthonormal this is the orthogonal projection onto $B_t$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 2.10, p.10; §3, p.11 (Π_{B_t} = Σ_{|Supp′(z)|≤t} |ẑ⟩⟨ẑ|)

import Mathlib
import Definitions.Def_QNoiseStab_fourierWeight
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QNoiseStab_ketBra

namespace QNoiseStab

/-- The projection `Π_{B_t}` onto the subspace `B_t` of input states of Fourier degree at most `t`
(Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space
Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
Definition 2.10, p.10: "Let Bt denote the subspace of the input registers spanned by Fourier basis
vectors |ẑ⟩ … such that at most t of the zi ≠ 0 … Define ΠBt to be the projection onto Bt"; and
p.11: "ΠBt = Σ_{|Supp′(z)|≤t} |ẑ⟩⟨ẑ|").

**Formalization Note** Defined by the p.11 formula, the sum of `|ẑ⟩⟨ẑ|` over the frequency vectors
`z` with at most `t` nonzero coordinates; since the `|ẑ⟩` (primitive root `exp(2πi/m)`) are an
orthonormal basis, this is the orthogonal projection onto `B_t`. -/
noncomputable def projLowDeg {n m : ℕ} [NeZero m] (t : ℕ) :
    Matrix (Fin n → ZMod m) (Fin n → ZMod m) ℂ :=
  ∑ z ∈ Finset.univ.filter (fun z : Fin n → ZMod m => fourierWeight z ≤ t), ketBra (fourierVec z)

end QNoiseStab


