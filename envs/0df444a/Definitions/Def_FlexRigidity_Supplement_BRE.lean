-- Prove2me | Definitions.Def_FlexRigidity_Supplement_BRE
-- name    : FlexRigidity_Supplement_BRE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:13:13.118346+00:00
-- url     : https://prove2.me/theorems/b73a6d38-6e56-4ab4-96c2-3add31567ab7
-- title:
--   Protocol 6 (sequential blind randomness expansion) — real rounds, guessing success, secrecy distance and honest acceptance
-- statement:
--   **Devices.** Under Postulate Set 5.4, in round $i$ Alice's device applies an instrument $\{\mathcal E^{A,x,a}_i\}_a$ to its memory $M^A_i$ and Bob — who receives $y_i$ and answers $b_i$ in every round of Protocol 6, and learns nothing else during it — applies an instrument $\{\mathcal E^{B,y,b}_i\}_b$ to his memory $M^B_i$; the memories have arbitrary finite dimension and the joint initial state $\rho^0$ of $R$, $M^A_1$, $M^B_1$ is arbitrary.
--
--   **Real round.** $x_i,y_i$ are uniform on $\{0,1,2\}$, the devices act as $\mathcal E^{A,x_i,a_i}_i\otimes\mathcal E^{B,y_i,b_i}_i$, and then $U_i=\mathrm{test}$ with probability $\gamma$. On a test $c_i=V(x_i,y_i,a_i,b_i)$; on a generation round $c_i=\mathrm{gen}$, $t_i$ is uniform on $\{0,1,2\}\setminus\{y_i\}$ and $k_i=a_i[t_i]$; the rest of $a_i$ is discarded. Alice accepts iff $\|\mathrm{freq}_c-P_C\|_{\mathrm{tr}}\le\varepsilon_{\mathrm{tol}}$ and there are at least $m$ generation positions; $E$ is the first $m$ of them and $K_E=(k_i)_{i\in E}$.
--
--   **Guessing.** With $Z=M^B_{n+1}R\,XYBCT$, the accepted guessing success of a measurement $\{G_k\}$ on $Z$ is $\sum_k\operatorname{Tr}[(|k\rangle\langle k|_{K_E}\otimes G_k)\rho_{K_EZ\wedge\mathrm{Acc}}]$; its maximum over measurements is $p_{\mathrm{Acc}}\,p_{\mathrm{guess}}(K_E\mid Z)_{\rho_{|\mathrm{Acc}}}$.
--
--   **Secrecy.** For a seed $D$ uniform on a finite set and a family $h_d:\{0,1\}^m\to\{0,1\}^\ell$, $L=h_D(K_E)$, the secrecy distance (80) is
--   $$\tfrac12\big\|\rho_{L\,R_{\mathrm{in}}C_{\mathrm{pub}}M^B_{\mathrm{fin}}\wedge\mathrm{Acc}}-\tfrac{I_L}{2^\ell}\otimes\rho_{R_{\mathrm{in}}C_{\mathrm{pub}}M^B_{\mathrm{fin}}\wedge\mathrm{Acc}}\big\|_1,$$
--   with $R_{\mathrm{in}}=XYUTD$, $C_{\mathrm{pub}}=DXYBCT$ and $M^B_{\mathrm{fin}}=M^B_{n+1}R$.
--
--   **Honest acceptance.** With a fresh copy of the honest Magic Square state and a perfect strategy in every round, $p_{\mathrm{Acc}}$ is the probability that the records pass the acceptance test.
--
--   These are the quantities of Theorem 6.14.
--
--   **Formalization Note** Rounds are numbered from $0$; the state after $n$ rounds is the published `FlexRigidity.seqRun` of the round channel. The guessing measurement may read the classical part $(c,x,y,b,t)$ of $Z$: for each value it is a POVM on Bob's quantum register; this loses nothing because the state is block diagonal in those registers. The operator in (80) is block diagonal in $L$, $D$ and the classical records, so its trace norm is the sum of the trace norms of the blocks. Alice's device memory is traced out.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Definition 6.4 p. 70, Protocol 6 p. 70, pp. 71–72 (Z, (80)), Theorem 6.14 p. 72

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_FlexRigidity_IsCPMap
import Definitions.Def_FlexRigidity_Hist
import Definitions.Def_FlexRigidity_seqRun
import Definitions.Def_FlexRigidity_genIdx
import Definitions.Def_FlexRigidity_PC
import Definitions.Def_FlexRigidity_freq
import Definitions.Def_FlexRigidity_quantumValue
import Definitions.Def_FlexRigidity_traceNorm
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_MagicSquare

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms (Superop IsChannel)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr)

noncomputable section

namespace FlexRigidity.Supplement

/-- **A device implementation and Bob attack for Protocol 6 under Postulate Set 5.4**
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Definition 6.4
and Protocol 6, p. 70): the memories before round `i` are `M^A_i = ℂ^{dA i}` (Alice's device) and
`M^B_i = ℂ^{dB i}` (Bob, his device and his memory), of arbitrary dimension. In round `i` Alice's
device is an instrument `{E^{A,x,a}_i}_a` for each input `x`, and Bob — who in Protocol 6 receives
`y_i` and answers `b_i` in **every** round, and learns nothing else during the protocol — applies an
instrument `{E^{B,y,b}_i}_b` for each `y`. The round's device channel is `E^A_i ⊗ E^B_i`.

`IsAllowed n`: for every round `i < n` the instrument elements are completely positive and each
instrument sums to a channel. -/
structure BRImpl (X Y A B : Type) where
  /-- dimension of Alice's device memory `M^A_i` -/
  dA : ℕ → ℕ
  /-- dimension of Bob's memory `M^B_i` -/
  dB : ℕ → ℕ
  /-- Alice's device instrument `E^{A,x,a}_i` -/
  EA : (i : ℕ) → X → A → Superop (Fin (dA i)) (Fin (dA (i + 1)))
  /-- Bob's instrument `E^{B,y,b}_i` -/
  EB : (i : ℕ) → Y → B → Superop (Fin (dB i)) (Fin (dB (i + 1)))

/-- The implementation is allowed for `n` rounds. -/
def BRImpl.IsAllowed {X Y A B : Type} [Fintype A] [Fintype B] (I : BRImpl X Y A B) (n : ℕ) : Prop :=
  ∀ i < n, (∀ x a, IsCPMap (I.EA i x a)) ∧ (∀ x, IsChannel (fun ρ => ∑ a, I.EA i x a ρ)) ∧
    (∀ y b, IsCPMap (I.EB i y b)) ∧ (∀ y, IsChannel (fun ρ => ∑ b, I.EB i y b ρ))

/-- The protected round output `O_i = U_i X_i Y_i B_i (T_i K_i)` of Protocol 6 (p. 72): `u = true`
on a test; `(t, k)` is present (`some`) exactly on a generation round, where `t ∈ {0,1,2} \ {y}` and
`k = a[t]`; on a test it is the dummy `none`. Alice's answer `a` itself is discarded. -/
abbrev BRO : Type := Bool × Fin 3 × Fin 3 × MSCol × Option (Fin 3 × Bool)

open Classical in
/-- **The real round channel of Protocol 6** (steps 1–2, p. 70; p. 72): `x_i, y_i` uniform; the
devices act as `E^{A,x,a}_i ⊗ E^{B,y,b}_i`; then `U_i = test` with probability `γ`. On a test the
record is `c_i = V(x, y, a, b)`; on a generation round `c_i = gen`, `t_i` is uniform on
`{0,1,2} \ {y_i}` and `k_i = a_i[t_i]`; the unused parts of `a_i` are discarded (summed over). The
output is classical on `(c_i, u_i, x_i, y_i, b_i, t_i, k_i)` (record alphabet `Option Bool`, `none`
= gen). -/
def breRound (γ : ℝ) (I : BRImpl (Fin 3) (Fin 3) MSRow MSCol) (i : ℕ) :
    Superop (Fin (I.dA i) × Fin (I.dB i))
      ((Option Bool × BRO) × (Fin (I.dA (i + 1)) × Fin (I.dB (i + 1)))) :=
  fun ρ => Matrix.of fun p q =>
    if p.1 = q.1 then
      (match p.1 with
        | (some w, (true, x, y, b, none)) =>
            ((γ * msGame.PXY x y : ℝ) : ℂ) *
              ∑ a ∈ Finset.univ.filter (fun a : MSRow => msGame.V x y a b = w),
                QAlgorithms.Papers.Independent.Information100.P62.tensorChannel
                  (I.EA i x a) (I.EB i y b) ρ p.2 q.2
        | (none, (false, x, y, b, some (t, k))) =>
            if t ≠ y then
              (((1 - γ) * msGame.PXY x y * (1 / 2) : ℝ) : ℂ) *
                ∑ a ∈ Finset.univ.filter (fun a : MSRow => a.1 t = k),
                  QAlgorithms.Papers.Independent.Information100.P62.tensorChannel
                    (I.EA i x a) (I.EB i y b) ρ p.2 q.2
            else 0
        | _ => 0)
    else 0

/-- The record histories of Protocol 6. -/
abbrev BRHist (n : ℕ) : Type := Hist (Option Bool) (fun _ => BRO) n

/-- **The real state of Protocol 6 after `n` rounds** on `C_{≤n} O_{≤n} ⊗ R ⊗ M^A_{n+1} M^B_{n+1}`,
from the initial state `ρ⁰_{M_1 R}` (the sequential process of Postulate Set 4.1). -/
def breState (γ : ℝ) (I : BRImpl (Fin 3) (Fin 3) MSRow MSCol) {r : ℕ}
    (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ)
    (n : ℕ) :
    Matrix (BRHist n × (Fin r × (Fin (I.dA n) × Fin (I.dB n))))
      (BRHist n × (Fin r × (Fin (I.dA n) × Fin (I.dB n)))) ℂ :=
  seqRun (C := Option Bool) (O := fun _ => BRO) (M := fun k => Fin (I.dA k) × Fin (I.dB k))
    (breRound γ I) ρ0 n

/-- The test/generation string `u` of a history. -/
def breU {n : ℕ} (h : BRHist n) : Fin n → Bool := fun i => (Hist.ent n h i).2.1

/-- **Acceptance** in Protocol 6 (step 3, p. 70): `‖freq_c − P_C‖_tr ≤ ε_tol`, `P_C` with the Magic
Square quantum value `ω*`; the requirement of at least `m` generation positions is imposed
separately wherever acceptance is used. -/
def breAcc (γ εtol : ℝ) {n : ℕ} (h : BRHist n) : Prop :=
  HybridXorLift.tvDist (freq (Hist.cs n h)) (PC γ (quantumValue msGame)) ≤ εtol

/-- The generation key bits `K_E = (k_i)_{i ∈ E}` on the first `m` generation positions `E`. -/
def breKE {n m : ℕ} (h : BRHist n) (hm : m ≤ (genSet (breU h)).card) : Fin m → Bool :=
  fun j => (((Hist.ent n h (genIdx (breU h) hm j)).2.2.2.2.2).map Prod.snd).getD false

/-- The classical part of `Z = M^B_{n+1} X Y B C T` in one round: `(c_i, x_i, y_i, b_i, t_i)`
(`t_i = none` on tests). -/
abbrev BRZCl : Type := Option Bool × Fin 3 × Fin 3 × MSCol × Option (Fin 3)

/-- The classical data `(c, x, y, b, t)` of a history. -/
def breZ {n : ℕ} (h : BRHist n) : Fin n → BRZCl :=
  fun i => ((Hist.ent n h i).1, (Hist.ent n h i).2.2.1, (Hist.ent n h i).2.2.2.1,
    (Hist.ent n h i).2.2.2.2.1, ((Hist.ent n h i).2.2.2.2.2).map Prod.fst)

/-- The public and input classical data of one round for the secrecy condition (80):
`(u_i, x_i, y_i, b_i, c_i, t_i)` (`R_in = XYUTD`, `C_pub = DXYBCT`; the seed `D` is kept apart). -/
abbrev BRPub : Type := Bool × Fin 3 × Fin 3 × MSCol × Option Bool × Option (Fin 3)

/-- The classical data `(u, x, y, b, c, t)` of a history. -/
def brePub {n : ℕ} (h : BRHist n) : Fin n → BRPub :=
  fun i => ((Hist.ent n h i).2.1, (Hist.ent n h i).2.2.1, (Hist.ent n h i).2.2.2.1,
    (Hist.ent n h i).2.2.2.2.1, (Hist.ent n h i).1, ((Hist.ent n h i).2.2.2.2.2).map Prod.fst)

/-- Bob's quantum register `R M^B_{n+1}` on the history `h`, Alice's device memory traced out
(it stays inaccessible to Bob, p. 70). -/
def breBob {n r dA dB : ℕ}
    (ρ : Matrix (BRHist n × (Fin r × (Fin dA × Fin dB))) (BRHist n × (Fin r × (Fin dA × Fin dB))) ℂ)
    (h : BRHist n) : Matrix (Fin r × Fin dB) (Fin r × Fin dB) ℂ :=
  Matrix.of fun p q => ∑ ma : Fin dA, ρ (h, (p.1, (ma, p.2))) (h, (q.1, (ma, q.2)))

open Classical in
/-- **The accepted guessing success** `Σ_k Tr[(|k⟩⟨k|_{K_E} ⊗ G_k) ρ_{K_E Z ∧ Acc}]` of a guessing
measurement on `Z = M^B_{n+1} R X Y B C T` (Definition (82), p. 72; guessing probability, p. 71).
The measurement `G` may read the classical part of `Z`: for each value of `(c, x, y, b, t)` it is a
POVM `{G_k}` on Bob's quantum register `R M^B_{n+1}`. Its maximum over `G` is
`p_Acc · p_guess(K_E | Z)_{ρ^real_{|Acc}}`. -/
def breGuess (γ εtol : ℝ) (n : ℕ) (I : BRImpl (Fin 3) (Fin 3) MSRow MSCol) {r : ℕ}
    (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ)
    (G : (Fin n → BRZCl) → (Fin (mLen γ n) → Bool) → Matrix (Fin r × Fin (I.dB n)) (Fin r × Fin (I.dB n)) ℂ) :
    ℝ :=
  ∑ h : BRHist n,
    if hh : breAcc γ εtol h ∧ mLen γ n ≤ (genSet (breU h)).card then
      tr (G (breZ h) (breKE h hh.2) * breBob (breState γ I ρ0 n) h)
    else 0

open Classical in
/-- **The secrecy distance of (80)** for Protocol 6 with the two-universal extractor
`L = h_D(K_E)` (Definition 6.4, p. 70; p. 71):
`½‖ρ_{L R_in C_pub M^B_fin ∧ Acc} − (I_L/2^ℓ) ⊗ ρ_{R_in C_pub M^B_fin ∧ Acc}‖₁`, with the seed `D`
uniform on the finite set `D`, independent, the classical registers `L, D, (u, x, y, b, c, t)` and
Bob's final quantum register `R M^B_{n+1}`. The operator is block diagonal in the classical
registers, so its trace norm is the sum over the blocks. -/
def breSecrecy (γ εtol : ℝ) (n : ℕ) (I : BRImpl (Fin 3) (Fin 3) MSRow MSCol) {r : ℕ}
    (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ)
    {D : Type} [Fintype D] (ℓ : ℕ) (hash : D → (Fin (mLen γ n) → Bool) → (Fin ℓ → Bool)) : ℝ :=
  (1 / 2) * ∑ d : D, ∑ l : Fin ℓ → Bool, ∑ cl : Fin n → BRPub,
    traceNorm (∑ h : BRHist n,
      if hh : breAcc γ εtol h ∧ mLen γ n ≤ (genSet (breU h)).card ∧ brePub h = cl then
        (((1 / (Fintype.card D : ℝ)) * ((if hash d (breKE h hh.2.1) = l then 1 else 0) - 1 / 2 ^ ℓ) : ℝ) : ℂ) •
          breBob (breState γ I ρ0 n) h
      else 0)

open Classical in
/-- **The honest acceptance probability of Protocol 6** (Theorem 6.14, p. 72; p. 60): each round uses
a fresh copy of `honestMS δ` and the perfect strategy `(T, N)`; `x, y` are uniform, `u = test` with
probability `γ`, the record is `V(x, y, a, b)` on a test and `gen` otherwise; Alice accepts iff
`‖freq_c − P_C‖_tr ≤ ε_tol` and there are at least `m` generation positions. -/
def brePAccHonest (δ γ εtol : ℝ) (n : ℕ)
    (T : Fin 3 → MSRow → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (N : Fin 3 → MSCol → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  ∑ t : Fin n → Bool × Fin 3 × Fin 3 × MSRow × MSCol,
    if HybridXorLift.tvDist
          (freq fun i => if (t i).1 then some (msGame.V (t i).2.1 (t i).2.2.1 (t i).2.2.2.1 (t i).2.2.2.2)
            else none)
          (PC γ (quantumValue msGame)) ≤ εtol ∧
        mLen γ n ≤ (Finset.univ.filter fun i => (t i).1 = false).card then
      ∏ i, (if (t i).1 then γ else 1 - γ) * msGame.PXY (t i).2.1 (t i).2.2.1 *
        tr (Matrix.kronecker (T (t i).2.1 (t i).2.2.2.1) (N (t i).2.2.1 (t i).2.2.2.2) * honestMS δ)
    else 0

end FlexRigidity.Supplement


