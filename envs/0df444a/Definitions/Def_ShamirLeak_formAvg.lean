-- Prove2me | Definitions.Def_ShamirLeak_formAvg
-- name    : ShamirLeak_formAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:59.357659+00:00
-- url     : https://prove2.me/theorems/229a6278-af98-4066-8ba2-775643e49d80
-- title:
--   Systems of affine-linear forms, independence, MDS systems, $\Lambda_\Psi$ and $q_t(r,k)$ (Definitions 12–13, Corollary 3)
-- statement:
--   Fix a prime $p$, integers $k\ge2$ and $r\ge1$, and write $V=\mathbb F_p^{k-1}$. A linear form on $V$ is $L(z)=\sum_{a=1}^{k-1}c_az_a$ with $c\in\mathbb F_p^{k-1}$, and an affine-linear form is $\psi=b+L$. For a system $\Psi=(\psi_i)_{i=1}^r$ with $\psi_i=b_i+L_i$:
--
--   1. a subfamily is **independent** if the coefficient vectors of its linear parts are linearly independent over $\mathbb F_p$ (the empty family is independent);
--   2. the system is **MDS** if every subfamily of at most $k-1$ forms is independent;
--   3. for $f=(f_1,\dots,f_r)$ with $f_i:\mathbb F_p\to\mathbb C$,
--   $$\Lambda_\Psi(f)=\mathbb E_{z\in V}\Big[\prod_{i=1}^rf_i(\psi_i(z))\Big].$$
--
--   Finally $q_t(r,k)=\lfloor(t(k-1)-r)/(t-1)\rfloor$ is the number of Gowers factors retained in Corollary 3.
--
--   The coordinates of a uniform GRS codeword are such a system (the MDS property comes from the Vandermonde determinant), so these averages carry the large-support estimates.
--
--   **Formalization Note** A system is given by its coefficient vectors `L : Fin r → (Fin (k - 1) → ZMod p)` and constants `b : Fin r → ZMod p`; $q_t(r,k)$ is an integer, the floor of a real quotient.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definitions 12–13, p.23 (PDF 25); Corollary 3, p.25 (PDF 27)

import Mathlib

namespace ShamirLeak

/-- An affine-linear form `ψ(z) = b + L(z)`, `L(z) = ∑_{a=1}^{k−1} c_a z_a`, on `V = 𝔽_p^{k−1}`
(Definition 12, p.23 (PDF p.25)), evaluated at `z`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 12, p.23 (PDF p.25).

**Formalization Note.** A system `Ψ = (ψᵢ)_{i=1}^r` is given by its coefficient vectors
`L : Fin r → (Fin (k − 1) → ZMod p)` (the linear parts) and constants `b : Fin r → ZMod p`. -/
def affineForm {p k : ℕ} (c : Fin (k - 1) → ZMod p) (b : ZMod p) (z : Fin (k - 1) → ZMod p) :
    ZMod p :=
  b + ∑ a, c a * z a

/-- A subfamily `(Lᵢ)_{i ∈ s}` of a system of forms is **independent** if its coefficient vectors
are linearly independent over `𝔽_p` (Definition 12, p.23 (PDF p.25)); the empty family is
independent (p.23).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 12, p.23. -/
def IndepForms {p k r : ℕ} (L : Fin r → (Fin (k - 1) → ZMod p)) (s : Finset (Fin r)) : Prop :=
  LinearIndependent (ZMod p) (fun i : s => L i)

/-- A system of forms is **MDS** if every subfamily of at most `k − 1` forms is independent
(Definition 12, p.23 (PDF p.25)); for affine forms this refers to the linear parts.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 12, p.23. -/
def IsMDSSystem {p k r : ℕ} (L : Fin r → (Fin (k - 1) → ZMod p)) : Prop :=
  ∀ s : Finset (Fin r), s.card ≤ k - 1 → IndepForms L s

/-- The **average along a system of forms** `Λ_Ψ(f) = E_{z ∈ V}[∏_{i=1}^r fᵢ(ψᵢ(z))]`
(Definition 13, p.23 (PDF p.25)), with `ψᵢ = bᵢ + Lᵢ` and `V = 𝔽_p^{k−1}`.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 13, p.23. -/
noncomputable def formAvg {p k r : ℕ} [NeZero p] (L : Fin r → (Fin (k - 1) → ZMod p))
    (b : Fin r → ZMod p) (f : Fin r → ZMod p → ℂ) : ℂ :=
  (∑ z : Fin (k - 1) → ZMod p, ∏ i, f i (affineForm (L i) (b i) z)) / ((p : ℂ) ^ (k - 1))

/-- The number of retained Gowers factors `q_t(r, k) = ⌊(t(k − 1) − r)/(t − 1)⌋`
(Corollary 3, p.25 (PDF p.27)); with `t = 3` and `r = n` it is the `q₃(n, k)` of Lemma 17.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Corollary 3, p.25.

**Formalization Note.** An integer (it may be zero or negative), computed as the floor of a real
quotient. -/
noncomputable def qt (t r k : ℕ) : ℤ :=
  ⌊((t : ℝ) * ((k : ℝ) - 1) - r) / ((t : ℝ) - 1)⌋

end ShamirLeak


