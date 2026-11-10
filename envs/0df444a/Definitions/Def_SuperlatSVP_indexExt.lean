-- Prove2me | Definitions.Def_SuperlatSVP_indexExt
-- name    : SuperlatSVP_indexExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:03.034615+00:00
-- url     : https://prove2.me/theorems/067ea12d-f755-4cbc-9e43-dc194208163f
-- title:
--   The index-$p$ extension $L_z=L+\mathbb Z\,B\bar z/p$ and the average over nonzero $z\in\mathbb F_p^n$
-- statement:
--   Let $L=B\mathbb Z^n$ be a full-rank lattice, $p$ a prime and $z\in\mathbb F_p^n$. Choose an integer representative $\bar z\in\mathbb Z^n$ of $z$. The **index-$p$ extension** of $L$ is the superlattice
--   $$L_z=L+\mathbb Z\,\frac{B\bar z}{p}.$$
--   For $z\ne0$ it has index $[L_z:L]=p$, and its dual is $L_z^*=B^{-T}K_z$ with $K_z=\{a\in\mathbb Z^n:\langle z,a\rangle\equiv0\bmod p\}$. Changing $\bar z$ by $p\,a$ moves $B\bar z/p$ by $Ba\in L$, so $L_z$ does not depend on the representative.
--
--   The expectation $\mathbb E_z$ over a uniformly random nonzero $z\in\mathbb F_p^n$ is
--   $$\mathbb E_z f(z)=\frac1{p^n-1}\sum_{z\in\mathbb F_p^n\setminus\{0\}}f(z).$$
--
--   The random lattice $\Gamma_0=L_z$ is the first superlattice of the paper's SVP algorithm.
--
--   **Formalization Note** $z$ is a vector in $(\mathbb Z/p)^n$ and its representative is taken coordinatewise in $\{0,\dots,p-1\}$. The average takes values in $[0,\infty]$.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3, (3.1)–(3.2), p.24 (PDF p.24)

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open scoped ENNReal

namespace SuperlatSVP

/-- The index-`p` extension `L_z = L + ℤ·B z̄ / p` of `L = Bℤⁿ` ((3.1), §3, p.24): "Let L = BZⁿ be
a full-rank lattice and p a prime. For z ∈ F_pⁿ ∖ {0} and any integer representative z̄, we define
the superlattice K_z = {a ∈ Zⁿ : ⟨z, a⟩ ≡ 0 mod p}, L_z = L + Z Bz̄/p with index [L_z : L] = p."

**Formalization Note.** `z : Fin n → ZMod p`; the representative `z̄` is taken coordinatewise as
`ZMod.val`. `L_z` does not depend on the representative (changing `z̄` by `p·a` changes `Bz̄/p` by
`Ba ∈ L`). -/
noncomputable def indexExt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) (z : Fin n → ZMod p) :
    Submodule ℤ (E n) :=
  lat B ⊔ Submodule.span ℤ {(1 / (p : ℝ)) • vecE (B.mulVec (fun i => ((z i).val : ℝ)))}

/-- The average `E_z f(z)` over a uniformly random nonzero `z ∈ F_pⁿ` (§3, p.24: "the expectation
is over a uniform random nonzero z ∈ F_pⁿ"): `(pⁿ − 1)⁻¹ ∑_{z ≠ 0} f(z)`.

**Formalization Note.** Values in `ℝ≥0∞`; `p` is assumed prime where this is used. -/
noncomputable def zAvg {n p : ℕ} [NeZero p] (f : (Fin n → ZMod p) → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ z ∈ (Finset.univ.filter fun z : Fin n → ZMod p => z ≠ 0), f z) / ((p ^ n - 1 : ℕ) : ℝ≥0∞)

end SuperlatSVP


