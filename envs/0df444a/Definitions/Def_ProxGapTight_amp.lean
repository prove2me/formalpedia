-- Prove2me | Definitions.Def_ProxGapTight_amp
-- name    : ProxGapTight_amp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:05.590563+00:00
-- url     : https://prove2.me/theorems/c16e84ea-57d6-470a-81f7-f9caa935e9fa
-- title:
--   Amplification map $A(v)_j=\ell_j(v_{i_{j,1}},\dots,v_{i_{j,t}})$
-- statement:
--   Let $\mathbb F$ be a field (in the paper $\mathbb F_q$) and $E$ an $\mathbb F$-vector space (in the paper $\mathbb F_{q^r}$). For each output coordinate $j\in[N]$ choose indices $i_{j,1},\dots,i_{j,t}\in[n]$ (with replacement) and an $\mathbb F$-linear functional $\ell_j:E^t\to\mathbb F$. The **amplification map** sends $v\in E^n$ to $A(v)\in\mathbb F^N$ with
--   $$
--   A(v)_j=\ell_j\big(v_{i_{j,1}},\dots,v_{i_{j,t}}\big).
--   $$
--
--   When the indices and functionals are uniform and independent, a word of relative weight $u$ is mapped to a word of relative weight about $(1-1/q)\Phi_t(u)$; this is how the small distances of the base code are amplified to arbitrary distances.
--
--   **Formalization Note** The choices for one coordinate form the finite set `AmpSample` (a tuple of indices together with a functional; it is finite when $\mathbb F$ and $E$ are finite), and a choice for all coordinates is a function from $[N]$ to it. Uniform independent sampling is then the uniform law on this finite set.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), proof of Theorem 3.1, p.13, display

import Mathlib

namespace ProxGapTight

/-- The randomness of **one coordinate** of the amplification map, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), proof of Theorem 3.1, p.13: `t` indices `i_{j,1}, …, i_{j,t} ∈ [n]`
(with replacement) and an `F`-linear functional `ℓ_j : E^t → F`.

**Formalization Note.** `[n]` is `Fin n`; the paper's `E = F_{q^r}` over `F = F_q` is any
`F`-module `E`. With `E` finite the type is finite (instance below), and "uniformly random" is the
uniform law on it. -/
abbrev AmpSample (F E : Type) [Field F] [AddCommGroup E] [Module F E] (n t : ℕ) : Type :=
  (Fin t → Fin n) × ((Fin t → E) →ₗ[F] F)

instance (F E : Type) [Field F] [Fintype F] [AddCommGroup E] [Module F E] [Fintype E]
    (n t : ℕ) : Finite (AmpSample F E n t) := by
  have : Finite ((Fin t → E) →ₗ[F] F) :=
    Finite.of_injective (fun f : (Fin t → E) →ₗ[F] F => (f : (Fin t → E) → F))
      DFunLike.coe_injective
  infer_instance

/-- The **amplification map** `A(v)_j := ℓ_j(v_{i_{j,1}}, …, v_{i_{j,t}})`, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), proof of Theorem 3.1, p.13, display. A sample `ω : Fin N → AmpSample`
gives, for each output coordinate `j ∈ [N]`, the indices `(ω j).1` and the functional `(ω j).2`.

**Formalization Note.** Independent uniform choices over `j ∈ [N]` are the uniform law on the
finite product `Fin N → AmpSample F E n t`; probabilities are counted as cardinality ratios. -/
def amp {F E : Type} [Field F] [AddCommGroup E] [Module F E] {n t N : ℕ}
    (ω : Fin N → AmpSample F E n t) (v : Fin n → E) : Fin N → F :=
  fun j => (ω j).2 (fun k => v ((ω j).1 k))

end ProxGapTight


