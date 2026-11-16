-- Prove2me | Definitions.Def_FlexRigidity_Supplement_UEHonest
-- name    : FlexRigidity_Supplement_UEHonest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:09:27.533202+00:00
-- url     : https://prove2.me/theorems/fb9658de-4f1d-4aac-94d3-c58ddac61fa8
-- title:
--   The honest run of Protocol 3 under depolarizing noise and its success probability
-- statement:
--   In the honest implementation of Protocol 3 each round uses a fresh copy of the noisy EPR pair $(1-2\sqrt2\delta_{\mathrm{hon}})|\phi\rangle\langle\phi|+2\sqrt2\delta_{\mathrm{hon}}I/4$; Alice samples $u_i$ ($\mathrm{test}$ with probability $\gamma$) and then $x_i$, which is the key bit $k_j$ on the $j$-th generation round with $j\le m$ and uniform otherwise; she measures $T^{x_i}$; on a test $y_i$ is uniform and Bob measures $N^{y_i}$; on a generation round Bob stores his half. To decrypt with key bits $\beta\in\{0,1\}^m$, Bob measures the stored half of the $j$-th round of $E$ in the basis $T^{\beta_j}$.
--
--   The **honest weight** of a record string $((u_i,x_i,y_i,a_i,b_i))_{i\le n}$, where on generation rounds $b_i$ is the outcome of Bob's later measurement, is the product over rounds of
--   - $(1-\gamma)\,[x_i=k_j]\operatorname{Tr}[(T^{x_i}_{a_i}\otimes T^{\beta_j}_{b_i})\rho_{\mathrm{hon}}]$ on the $j$-th generation round, $j\le m$;
--   - $(1-\gamma)\tfrac12\operatorname{Tr}[(T^{x_i}_{a_i}\otimes T^{x_i}_{b_i})\rho_{\mathrm{hon}}]$ on later generation rounds (whose $b_i$ is never used);
--   - $\gamma\tfrac14\operatorname{Tr}[(T^{x_i}_{a_i}\otimes N^{y_i}_{b_i})\rho_{\mathrm{hon}}]$ on a test.
--
--   With $k$ uniform and $\beta=k$,
--   $$\Pr_{P'}[\mathrm{Acc}\wedge(\text{Honest Bob decrypts correctly})]=\sum_k2^{-m}\sum_t w_{k,k}(t)\,\big[\mathrm{Acc}(t)\wedge\mathrm{dec}(\mathrm{syn}(a_E),b_E)=a_E\big],$$
--   since the recovered plaintext $\mathrm{dec}(\mathrm{syn}(a_E),b_E)\oplus c_{\mathrm{msg}}$ equals $\mathbf m$ exactly when $\mathrm{dec}(\mathrm{syn}(a_E),b_E)=a_E$.
--
--   This is the completeness quantity of Theorem 6.6; the weights with prescribed key $y$ and bases $x$ give the honest evaluation of Protocol 5 (Theorem 6.10).
--
--   **Formalization Note** The rounds of the honest implementation are independent and identical (p. 60), so the joint law of all classical outcomes is this product; recording Bob's later decrypting outcome in the generation record does not change any marginal.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), §6 p. 60 (noise model), Protocol 3 p. 63, Theorem 6.6 p. 64

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_CHSH
import Definitions.Def_FlexRigidity_RoundO
import Definitions.Def_FlexRigidity_recordOf
import Definitions.Def_FlexRigidity_genIdx
import Definitions.Def_FlexRigidity_PC
import Definitions.Def_FlexRigidity_freq
import Definitions.Def_FlexRigidity_quantumValue
import Definitions.Def_HybridXorLift_tvDist

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr)

noncomputable section

namespace FlexRigidity.Supplement

/-- The number of generation rounds strictly before round `i` (so round `i`, if it is a generation
round, is the `(genPos u i + 1)`-th one). -/
def genPos {n : ℕ} (u : Fin n → Bool) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun i' => i' < i ∧ u i' = false).card

/-- **One factor of the honest law of Protocol 3's preparation and decryption** (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Protocol 3, p. 63, and the honest
noise model, p. 60). Each round uses a fresh noisy EPR pair `honestCHSH δ`; Alice measures `T^{x}`;
on a test (`u = true`, probability `γ`) `y` is uniform and Bob measures `N^y`; on a generation round
Bob stores his half. For the `(j+1)`-th generation round with `j < m`, Alice's input is the key bit
`key_j`, and the record's `b` is the outcome of the decrypting measurement `T^{bas_j}` that Bob later
applies to the stored half (basis `bas_j`). On later generation rounds `x` is uniform and `b` is the
outcome of `T^x` (never used, so only the marginal of `a` matters). Records of any other shape have
probability `0`. -/
def honestFactor (δ γ : ℝ) {m : ℕ} (key bas : Fin m → Bool) (j : ℕ) :
    RoundO Bool Bool Bool Bool → ℝ
  | (false, x, none, a, some b) =>
      if h : j < m then
        (1 - γ) * (if x = key ⟨j, h⟩ then 1 else 0) *
          tr (Matrix.kronecker (wiesnerT x a) (wiesnerT (bas ⟨j, h⟩) b) * honestCHSH δ)
      else
        (1 - γ) * wiesnerRz.PX x *
          tr (Matrix.kronecker (wiesnerT x a) (wiesnerT x b) * honestCHSH δ)
  | (true, x, some y, a, some b) =>
      γ * chshGame.PXY x y * tr (Matrix.kronecker (wiesnerT x a) (chshN y b) * honestCHSH δ)
  | _ => 0

/-- **The honest probability of a complete round record string** `t = ((u_i, x_i, y_i, a_i, b_i))_i`
of Protocol 3 with prescribed key `key ∈ {0,1}^m` and Bob's decryption bases `bas` (pp. 60, 63):
the rounds are independent given their position among the generation rounds. -/
def honestWeight (δ γ : ℝ) {n m : ℕ} (key bas : Fin m → Bool)
    (t : Fin n → RoundO Bool Bool Bool Bool) : ℝ :=
  ∏ i, honestFactor δ γ key bas (genPos (fun i => (t i).1) i) (t i)

/-- Honest acceptance of Protocol 3's preparation: `‖freq_c − P_C‖_tr ≤ ε_tol` for the records
`c_i = g(u_i, x_i, y_i, a_i, b_i)` (Protocol 2, p. 41). -/
def honestAcc (γ εtol : ℝ) {n : ℕ} (t : Fin n → RoundO Bool Bool Bool Bool) : Prop :=
  HybridXorLift.tvDist (freq fun i => recordOf chshGame (t i)) (PC γ (quantumValue chshGame)) ≤ εtol

/-- Alice's raw string `a_E` on the first `m` generation rounds `E`. -/
def honestAE {n m : ℕ} (t : Fin n → RoundO Bool Bool Bool Bool)
    (hm : m ≤ (genSet fun i => (t i).1).card) : Fin m → Bool :=
  fun j => (t (genIdx (fun i => (t i).1) hm j)).2.2.2.1

/-- Honest Bob's decryption outcomes `b_E` on his stored halves of the rounds in `E`. -/
def honestBE {n m : ℕ} (t : Fin n → RoundO Bool Bool Bool Bool)
    (hm : m ≤ (genSet fun i => (t i).1).card) : Fin m → Bool :=
  fun j => ((t (genIdx (fun i => (t i).1) hm j)).2.2.2.2).getD false

open Classical in
/-- **`Pr_{P′}[Acc ∧ (Honest Bob decrypts correctly)]`** for Protocol 3 (Theorem 6.6, p. 64): the key
`k` is uniform, the honest preparation with depolarizing noise `2√2 δ_hon` runs, Alice accepts, and
Bob, measuring his stored halves of `E` in the bases `k` and correcting with the syndrome
`syn(a_E)`, recovers `a_E` (then `c_msg ⊕ a_E` is the plaintext, for every plaintext). -/
def ueHonestSucc (δ γ εtol : ℝ) (n : ℕ) {s : ℕ} (syn : (Fin (mLen γ n) → Bool) → Fin s → Bool)
    (dec : (Fin s → Bool) → (Fin (mLen γ n) → Bool) → (Fin (mLen γ n) → Bool)) : ℝ :=
  ∑ k : Fin (mLen γ n) → Bool, (1 / 2 ^ mLen γ n : ℝ) *
    ∑ t : Fin n → RoundO Bool Bool Bool Bool,
      honestWeight δ γ k k t *
        (if h : honestAcc γ εtol t ∧ mLen γ n ≤ (genSet fun i => (t i).1).card then
          (if dec (syn (honestAE t h.2)) (honestBE t h.2) = honestAE t h.2 then 1 else 0)
        else 0)

end FlexRigidity.Supplement


