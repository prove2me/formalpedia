-- Prove2me | Definitions.Def_DetANN_Construction
-- name    : DetANN_Construction
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T17:40:34.084197+00:00
-- url     : https://prove2.me/theorems/f335507c-0d44-435b-9c5f-154e321e6026
-- title:
--   The explicit construction of Theorem 1.1 (§7.4)
-- statement:
--   Fix points $P_1,\dots,P_n\in\mathbb R^d$, an integer $k$, $\varepsilon\in(0,1)$ and a constant $C_0$.
--
--   1. **Padding.** $\mathrm{pad}:\mathbb R^d\to\mathbb R^{2^k}$ appends zeros (and drops coordinates if $d>2^k$). The padded point set is $\{\mathrm{pad}(P_i)\}$, and $\mathcal D=\{\mathrm{pad}(P_i)-\mathrm{pad}(P_j): i<j\}$.
--   2. **Parameters.** $\tau=\varepsilon^2/10^6$ as in (12), $p_0=\lceil\log_4(8|\mathcal D|\,2^k)\rceil$ and $L=\lceil C_0\tau^{-2}p_0\rceil$.
--   3. **Blocks.** The signed blocks of §6.1 built from the Sylvester–Hadamard matrix $H_k$ (definition `DetANN_Sylvester`) with the greedy signs of the definition `DetANN_SignChoice`, scored by the Lemma 6.2 expression.
--   4. **Tuples.** The walk length $\ell=\lceil\log_{1/\theta_0}(200/\varepsilon)\rceil$ of §7.4, and the tuples $S_v$ of endpoints of all length-$\ell$ walks from $v$ in the Lemma 7.1 graph on $\mathrm{Fin}(2^k)$.
--
--   These are the data structure's blocks and tuples whose correctness is the content of §7.4.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.4, p.19, with (12), p.9, §6.1, p.14 and §7.1, p.17

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_SignChoice
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_MGG

namespace DetANN

/-!
# The explicit construction of Theorem 1.1 (§7.4)

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.4, p.19, with §6 for the blocks and §7.1 for the
tuples. The dimension is padded to a power of two `2^k ≥ d`.
-/

/-- Pad `x ∈ ℝ^d` with zeros to a vector of `ℝ^m`. -/
noncomputable def padVec {d : ℕ} (m : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun r => if h : (r : ℕ) < d then x.ofLp ⟨r, h⟩ else 0

/-- The padded point set `{pad(P i)}` in `ℝ^{2^k}`. -/
noncomputable def paddedSet {d n : ℕ} (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d)) :
    Finset (EuclideanSpace ℝ (Fin (2 ^ k))) :=
  Finset.univ.image fun i => padVec (2 ^ k) (P i)

/-- The differences `pad(P i) − pad(P j)` for `i < j`. -/
noncomputable def diffSet {d n : ℕ} (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d)) :
    Finset (EuclideanSpace ℝ (Fin (2 ^ k))) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2).image
    fun p => padVec (2 ^ k) (P p.1) - padVec (2 ^ k) (P p.2)

/-- The balance parameter `τ = ε²/10⁶` of (12). -/
noncomputable def annTau (ε : ℝ) : ℝ := ε ^ 2 / 10 ^ 6

/-- The number of repetitions `L = ⌈C₀ τ⁻² p₀⌉` with `p₀ = ⌈log₄(8Nd)⌉`, `N = |𝒟|`, `d = 2^k`. -/
noncomputable def annReps {d n : ℕ} (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d))
    (ε : ℝ) : ℕ :=
  numReps C₀ (annTau ε) (momentOrder (diffSet k P).card (2 ^ k))

/-- The blocks of Theorem 3.2 for the padded points: Sylvester matrix, signs chosen greedily by the
Lemma 6.2 expression. -/
noncomputable def annBlocks {d n : ℕ} (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d))
    (ε : ℝ) (j : Fin (2 ^ k)) :
    EuclideanSpace ℝ (Fin (2 ^ k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (annReps C₀ k P ε)) :=
  signedBlocks (sylvester k) (annReps C₀ k P ε)
    (greedySigns (lemma62Expr (sylvester k) (annReps C₀ k P ε) (annTau ε)
      (momentOrder (diffSet k P).card (2 ^ k)) (diffSet k P)) (annReps C₀ k P ε * 2 ^ k)) j

/-- The walk length `ℓ = ⌈log_{1/θ₀}(200/ε)⌉` of §7.4. -/
noncomputable def walkLen (ε : ℝ) : ℕ := ⌈Real.logb (1 / theta0) (200 / ε)⌉₊

/-- The tuples of §7.1: endpoints of all length-`ℓ` walks in the Lemma 7.1 graph on `Fin (2^k)`. -/
noncomputable def annTuples (k : ℕ) (ε : ℝ) : Fin (2 ^ k) → (Fin (walkLen ε) → Fin 16) → Fin (2 ^ k) :=
  walkEnd (lemma71Nbr k) (walkLen ε)

end DetANN


