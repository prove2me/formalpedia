-- Prove2me | Definitions.Def_FlexRigidity_Supplement_UE
-- name    : FlexRigidity_Supplement_UE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:08:29.173194+00:00
-- url     : https://prove2.me/theorems/09186eaa-b0c5-406f-948f-e7bc14ef78fd
-- title:
--   Protocol 3's accepted preparation and the uncloneable-encryption search experiment (Definition 6.1)
-- statement:
--   **Preparation.** Protocol 3 runs the preparation phase of Protocol 2 with the CHSH game for $n$ rounds, testing probability $\gamma$ and tolerance $\varepsilon_{\mathrm{tol}}$, with any device implementation allowed by Postulate Set 5.4 (Alice's device instruments $\mathcal E^{A,x,a}_i$, Bob's operations) and any normalized initial state $\rho^0_{M_1R}$. Alice accepts ($\mathrm{Acc}$) iff $\|\mathrm{freq}_c-P_C\|_{\mathrm{tr}}\le\varepsilon_{\mathrm{tol}}$, with $P_C=(1-\gamma,\gamma\omega^*,\gamma(1-\omega^*))$ and $\omega^*$ the quantum value of CHSH; $E$ is the set of the first $m=\lfloor(1-\gamma)n/2\rfloor$ generation rounds. The key is $k=x_E$ and Alice's raw string is $a_E$. For each $(k,a)$, $\rho^B_{k,a}$ denotes the subnormalized state of Bob's register (his memory $M^B_{n+1}$, the external information $R$ and his transcript $(u_i,y_i,b_i)$) on the event $\mathrm{Acc}\wedge(x_E,a_E)=(k,a)$; Alice's device memory is traced out. Its total trace is $p_{\mathrm{Acc}}=\Pr[\mathrm{Acc}]$.
--
--   **Search experiment.** On acceptance, the plaintext $\mathbf m$ is uniform on $\{0,1\}^m$; Alice publishes $c_{\mathrm{msg}}=\mathbf m\oplus a_E$ and the syndrome $\sigma=\mathrm{syn}(a_E)$. Bob applies a channel $\Lambda_{c_{\mathrm{msg}},\sigma}$ from his register to the registers $D_1\otimes D_2$ of two decoders; decoder $j$, given the complete key $k$, measures a POVM on $D_j$ and outputs $\mathbf m_j\in\{0,1\}^m$. Then
--   $$\Pr_{\mathrm{DI}}[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{search}}]=\sum_{k,a}\sum_{\mathbf m}2^{-m}\operatorname{Tr}\big[(F^1_{k,c,\sigma}(\mathbf m)\otimes F^2_{k,c,\sigma}(\mathbf m))\,\Lambda_{c,\sigma}(\rho^B_{k,a})\big],\quad c=\mathbf m\oplus a,\ \sigma=\mathrm{syn}(a).$$
--   Protocol 3 with syndrome function $\mathrm{syn}$ is **$\delta_{\mathrm{UE}}$-search secure** if this is at most $\delta_{\mathrm{UE}}$ for every allowed implementation, initial state, splitting channel and decoders.
--
--   These are the objects of Theorems 6.6, 6.8 and 6.10.
--
--   **Formalization Note** The preparation is the published `FlexRigidity.seqRun` of `FlexRigidity.realRound` with `FlexRigidity.finalOp` on acceptance, exactly as in the published Theorem 5.6. Alice's choice $x_i=k_j$ on the $j$-th generation round, with $k$ uniform, gives exactly Protocol 2's joint law (p. 63), so $k$ is read off as $x_E$. The decoders' measurements may depend on the public classical data $(c_{\mathrm{msg}},\sigma)$, which Bob can copy to both; all registers are finite-dimensional.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Definition 6.1 pp. 60–61, Protocol 3 p. 63, Protocol 2 pp. 40–41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_CHSH
import Definitions.Def_FlexRigidity_realRound
import Definitions.Def_FlexRigidity_seqRun
import Definitions.Def_FlexRigidity_finalOp
import Definitions.Def_FlexRigidity_PC
import Definitions.Def_FlexRigidity_freq
import Definitions.Def_HybridXorLift_tvDist

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms (Superop IsChannel)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density POVM)

noncomputable section

namespace FlexRigidity.Supplement

/-- The record histories of Protocol 3's preparation phase (Protocol 2 with the CHSH game). -/
abbrev UEHist (n : ℕ) : Type := Hist (Option Bool) (fun _ => RoundO Bool Bool Bool Bool) n

/-- **Acceptance** `Acc_{ε_tol}` of Protocol 3's preparation (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Protocol 3 step 2(b), p. 63, and Protocol 2, pp. 40–41):
`‖freq_c − P_C‖_tr ≤ ε_tol`, `P_C = (1 − γ, γω*, γ(1 − ω*))` with `ω*` the quantum value of CHSH.
(The requirement of at least `m` generation rounds is imposed by `finalOp`.) -/
def ueAcc (γ εtol : ℝ) {n : ℕ} (h : UEHist n) : Prop :=
  HybridXorLift.tvDist (freq (Hist.cs n h)) (PC γ (quantumValue chshGame)) ≤ εtol

/-- The dimension of Bob's register after preparation: his transcript `(u_i, y_i, b_i)_{i ≤ n}`,
the external information `R = ℂ^r` and his memory `M^B_{n+1}` (base Reading 8). -/
def ueBobDim (n r : ℕ) (I : DIImpl Bool Bool Bool Bool) : ℕ :=
  Fintype.card ((Fin n → Bool × Option Bool × Option Bool) × (Fin r × Fin (I.dB n)))

open Classical in
/-- **The accepted output of Protocol 3's preparation** (p. 63): Protocol 2 with the CHSH game and
the Wiesner realization is run for `n` rounds with the device implementation `I` (Postulate Set
5.4) on the initial state `ρ⁰_{M_1 R}`; on acceptance with `E` the first `m = ⌊(1 − γ)n/2⌋`
generation rounds, Alice keeps `(x_E, a_E)` and Bob keeps his register. `ueBlock … xa` is the
subnormalized operator on Bob's register on the event `Acc ∧ (x_E, a_E) = xa`.

**Formalization Note** The key is `k = x_E` (p. 63: "On acceptance, `x_E = k`"). Alice's choice
`x_i = k_j` on the `j`-th generation round with `k` uniform and her uniform `x_i` on all other rounds
give exactly Protocol 2's joint law of `(U, X, Y)` and of the device inputs (p. 63), so `k` is read
off as `x_E` of Protocol 2's run. -/
def ueBlock (γ εtol : ℝ) (n : ℕ) (I : DIImpl Bool Bool Bool Bool) {r : ℕ}
    (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ)
    (xa : Fin (mLen γ n) → Bool × Bool) :
    Matrix (Fin (ueBobDim n r I)) (Fin (ueBobDim n r I)) ℂ :=
  let ρ := finalOp (mLen γ n) (ueAcc γ εtol)
    (seqRun (M := fun k => Fin (I.dA k) × Fin (I.dB k)) (realRound chshGame wiesnerRz γ I) ρ0 n)
  Matrix.of fun i j => ρ (xa, i) (xa, j)

/-- The acceptance probability `p_Acc = Pr[Acc]` of a preparation, the trace of its accepted
output. -/
def accProb {m d : ℕ} (ρB : (Fin m → Bool × Bool) → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ xa, tr (ρB xa)

/-- **An attack in the search experiment after preparation** (Definition 6.1, steps 3–4, pp. 60–61):
Bob's splitting channel `Λ_{c,σ}` from his register to the decoders' registers `D_1 ⊗ D_2`, which may
depend on the public ciphertext `c_msg` and syndrome `σ`, and the decoders' measurements
`F^j_{k,c,σ}` with outcome `m_j ∈ {0,1}^m`, each acting on its own register only and depending on the
complete key `k` and on the public data. -/
structure SearchAttack (m s d : ℕ) where
  /-- dimension of decoder 1's register -/
  d1 : ℕ
  /-- dimension of decoder 2's register -/
  d2 : ℕ
  /-- Bob's splitting channel -/
  Λ : (Fin m → Bool) → (Fin s → Bool) → Superop (Fin d) (Fin d1 × Fin d2)
  /-- decoder 1's measurement, given key, ciphertext and syndrome -/
  F1 : (Fin m → Bool) → (Fin m → Bool) → (Fin s → Bool) → (Fin m → Bool) → Matrix (Fin d1) (Fin d1) ℂ
  /-- decoder 2's measurement, given key, ciphertext and syndrome -/
  F2 : (Fin m → Bool) → (Fin m → Bool) → (Fin s → Bool) → (Fin m → Bool) → Matrix (Fin d2) (Fin d2) ℂ

/-- The splitting maps are channels and the decoders' measurements are POVMs. -/
def SearchAttack.IsValid {m s d : ℕ} (att : SearchAttack m s d) : Prop :=
  (∀ c σ, IsChannel (att.Λ c σ)) ∧ (∀ k c σ, POVM (att.F1 k c σ)) ∧ (∀ k c σ, POVM (att.F2 k c σ))

/-- **`Pr[Acc ∧ Bad_search]`** in the search experiment of Definition 6.1 for Protocol 3 (pp. 60–63):
on acceptance with `(x_E, a_E) = (k, a)`, the plaintext `msg` is uniform on `{0,1}^m`, Alice publishes
`c_msg = msg ⊕ a` and the syndrome `syn(a)`, Bob splits, and both decoders output `msg`. -/
def searchSucc {m s d : ℕ} (ρB : (Fin m → Bool × Bool) → Matrix (Fin d) (Fin d) ℂ)
    (syn : (Fin m → Bool) → Fin s → Bool) (att : SearchAttack m s d) : ℝ :=
  ∑ xa : Fin m → Bool × Bool, ∑ msg : Fin m → Bool,
    (1 / 2 ^ m : ℝ) *
      tr (Matrix.kronecker (att.F1 (fun j => (xa j).1) (xorS msg fun j => (xa j).2)
            (syn fun j => (xa j).2) msg)
          (att.F2 (fun j => (xa j).1) (xorS msg fun j => (xa j).2) (syn fun j => (xa j).2) msg) *
        att.Λ (xorS msg fun j => (xa j).2) (syn fun j => (xa j).2) (ρB xa))

/-- **`δ_UE`-search security of Protocol 3** (Definition 6.1, p. 61): for the parameters `n, γ, ε_tol`
and the syndrome function `syn`, every allowed attack — every device implementation and Bob
strategy allowed by Postulate Set 5.4, every initial state `ρ⁰_{M_1 R}` and every splitting and
decoding — has `Pr_DI[Acc ∧ Bad_search] ≤ δ_UE`. -/
def IsSearchSecure (γ εtol : ℝ) (n : ℕ) {s : ℕ} (syn : (Fin (mLen γ n) → Bool) → Fin s → Bool)
    (δUE : ℝ) : Prop :=
  ∀ I : DIImpl Bool Bool Bool Bool, I.IsAllowed n →
  ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
      (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
  ∀ att : SearchAttack (mLen γ n) s (ueBobDim n r I), att.IsValid →
    searchSucc (ueBlock γ εtol n I ρ0) syn att ≤ δUE

end FlexRigidity.Supplement


