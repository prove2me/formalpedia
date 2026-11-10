-- Prove2me | Definitions.Def_DQILocal_Recon_Ensembles
-- name    : DQILocal_Recon_Ensembles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:01.298122+00:00
-- url     : https://prove2.me/theorems/9fe05fd6-a96e-4168-a315-49981a5ca1dc
-- title:
--   The configuration model and Gallager's ensemble: probability of $\mathrm{LT}_t(i)\wedge\mathrm{TP}_t(i)$
-- statement:
--   Two ensembles of random $(k,D)$-regular instances over $\mathbb Z_q$ (§5.1):
--
--   1. **Configuration model** ($D\mid km$, $n=km/D$ checks): give each symbol $k$ half-edges and each check $D$ half-edges, pair them by a uniformly random bijection, and condition on no multiple edges. The resulting matrix $B$ is uniform among the $(k,D)$-regular $m\times n$ 0/1 matrices.
--   2. **Gallager's ensemble** ($D\mid m$): the checks come in $k$ layers, each a partition of the $m$ symbols into $m/D$ blocks of size $D$. The first layer is the fixed partition into consecutive blocks; layer $\ell$ is its image under a permutation $\sigma_\ell$, with $\sigma_2,\dots,\sigma_k$ independent and uniform.
--
--   For each ensemble, the defined quantities are $\Pr[\mathrm{LT}_t(i)\wedge\mathrm{TP}_t(i)]$ for a symbol $i$ uniform on $[m]$ independent of $B$, and $\Pr_B[\mathrm{LT}_t(i)\wedge\mathrm{TP}_t(i)]$ for a fixed symbol $i$.
--
--   **Formalization Note** Each simple $(k,D)$-biregular labelled graph arises from exactly $(k!)^m(D!)^n$ bijections, so the conditioned configuration model is the uniform law on regular matrices (as p. 3 states). Probabilities are counting ratios over finite sets; when no regular matrix exists (finitely many $m$) the ratio is $0$. Gallager's checks are indexed by (layer, block), and symbol $j$ lies in check $(\ell,b)$ iff $\lfloor\sigma_\ell^{-1}(j)/D\rfloor=b$.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §5.1, p. 31; p. 3

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions

namespace DQILocal.Recon

open scoped BigOperators

/-- **The configuration model (§5.1, p. 31), probability of the local conditions at a uniformly
random symbol.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §5.1, p. 31; p. 3
("`B` is uniformly random among such matrices").

For `m` symbols and `n = km/D` checks, `B` is uniform on the `(k, D)`-regular `m × n` 0/1 matrices
and `i` is uniform on `[m]`, independent of `B`; `configProb k D q t m` is
`Pr[LT_t(i) ∧ TP_t(i)]`.

**Formalization Note.** The paper pairs half-edges by a uniformly random bijection and conditions
on no multiple edges; every simple `(k, D)`-biregular labelled graph arises from exactly
`(k!)^m (D!)^n` bijections, so the conditioned law is the uniform law on the `(k, D)`-regular
matrices. The model is used only when `D ∣ km`; when there is no regular matrix (finitely many
`m`) the quotient is `0`. -/
noncomputable def configProb (k D q t m : ℕ) : ℝ := by
  classical
  exact
    ((Finset.univ.filter fun Bi : Matrix (Fin m) (Fin (k * m / D)) Bool × Fin m =>
        IsRegular k D Bi.1 ∧ LT Bi.1 Bi.2 t ∧ TP q Bi.1 Bi.2 t).card : ℝ) /
      ((Finset.univ.filter fun Bi : Matrix (Fin m) (Fin (k * m / D)) Bool × Fin m =>
        IsRegular k D Bi.1).card : ℝ)

/-- The configuration model, probability of the local conditions at a fixed symbol `i`:
`Pr_B[LT_t(i) ∧ TP_t(i)]` with `B` uniform on the `(k, D)`-regular `m × (km/D)` matrices. -/
noncomputable def configProbAt (k D q t m : ℕ) (i : Fin m) : ℝ := by
  classical
  exact
    ((Finset.univ.filter fun B : Matrix (Fin m) (Fin (k * m / D)) Bool =>
        IsRegular k D B ∧ LT B i t ∧ TP q B i t).card : ℝ) /
      ((Finset.univ.filter fun B : Matrix (Fin m) (Fin (k * m / D)) Bool =>
        IsRegular k D B).card : ℝ)

/-- **Gallager's matrix (§5.1, p. 31).** Checks are indexed by (layer `ℓ ∈ [k]`, block
`b ∈ [m/D]`). Layer `ℓ` is the image under the permutation `σ_ℓ` of the fixed partition of the `m`
symbols into the consecutive blocks `{bD, …, bD + D - 1}`: symbol `j` is in check `(ℓ, b)` iff
`⌊σ_ℓ⁻¹(j) / D⌋ = b`. -/
def gallagerMatrix (k D m : ℕ) (σ : Fin k → Equiv.Perm (Fin m)) :
    Matrix (Fin m) (Fin k × Fin (m / D)) Bool :=
  fun j lb => decide (((σ lb.1).symm j).val / D = lb.2.val)

/-- **Gallager's ensemble (§5.1, p. 31), probability of the local conditions at a uniformly random
symbol.** The first layer is fixed (`σ` of layer `0` is the identity) and the permutations of the
other `k - 1` layers are independent and uniform; `i` is uniform on `[m]`, independent of them. The
ensemble is used only when `D ∣ m`. -/
noncomputable def gallagerProb (k D q t m : ℕ) : ℝ := by
  classical
  exact
    ((Finset.univ.filter fun σi : (Fin k → Equiv.Perm (Fin m)) × Fin m =>
        (∀ ℓ : Fin k, ℓ.val = 0 → σi.1 ℓ = 1) ∧
          LT (gallagerMatrix k D m σi.1) σi.2 t ∧ TP q (gallagerMatrix k D m σi.1) σi.2 t).card :
        ℝ) /
      ((Finset.univ.filter fun σi : (Fin k → Equiv.Perm (Fin m)) × Fin m =>
        (∀ ℓ : Fin k, ℓ.val = 0 → σi.1 ℓ = 1)).card : ℝ)

/-- Gallager's ensemble, probability of the local conditions at a fixed symbol `i`. -/
noncomputable def gallagerProbAt (k D q t m : ℕ) (i : Fin m) : ℝ := by
  classical
  exact
    ((Finset.univ.filter fun σ : Fin k → Equiv.Perm (Fin m) =>
        (∀ ℓ : Fin k, ℓ.val = 0 → σ ℓ = 1) ∧
          LT (gallagerMatrix k D m σ) i t ∧ TP q (gallagerMatrix k D m σ) i t).card : ℝ) /
      ((Finset.univ.filter fun σ : Fin k → Equiv.Perm (Fin m) =>
        (∀ ℓ : Fin k, ℓ.val = 0 → σ ℓ = 1)).card : ℝ)

end DQILocal.Recon


