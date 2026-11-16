-- Prove2me | Definitions.Def_FlexRigidity_Supplement_CopyProtection
-- name    : FlexRigidity_Supplement_CopyProtection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:11:21.947497+00:00
-- url     : https://prove2.me/theorems/66801f43-4503-471b-853c-8b9866f77b0e
-- title:
--   Point functions $P_{y,v}$, Protocol 5, and the copy-protection experiment (Definition 6.3)
-- statement:
--   The **multi-bit point function** with marked input $y\in\{0,1\}^m$ and value $v\in\{0,1\}^m$ is $P_{y,v}(x)=v$ if $x=y$ and $0^m$ otherwise.
--
--   **Protocol 5** (hash length $\tau$) runs Protocol 3's preparation with key $k=y$; on acceptance Alice publishes $c_{\mathrm{msg}}=v\oplus a_E$, the syndrome $\sigma=\mathrm{syn}(a_E)$, a uniform binary $\tau\times m$ matrix $R$ and $z=Ry$. Evaluation at $x$ returns $0^m$ if $Rx\ne z$ and otherwise runs Protocol 3's honest decryption with key $x$.
--
--   **Copy-protection experiment.** $y,v$ are uniform and independent; on acceptance Bob splits everything he holds by a channel $\Lambda_{c,\sigma,R,z}$ between two decoders; independently for $j=1,2$, $X^{(j)}=y$ with probability $\tfrac12$ and otherwise uniform on $\{0,1\}^m\setminus\{y\}$, given only to decoder $j$, which outputs $V^{(j)}$ by a measurement on its register. Then
--   $$\Pr[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{copy}}],\qquad \mathrm{Bad}_{\mathrm{copy}}=(V^{(1)}=P_{y,v}(X^{(1)}))\wedge(V^{(2)}=P_{y,v}(X^{(2)})),$$
--   is false on abort; the **piracy advantage** is $\Pr[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{copy}}]-\Pr[\mathrm{Acc}]/2$.
--
--   The **honest pointwise failure** at fixed $(y,v,x)$ is the probability that the honest preparation (depolarizing noise $2\sqrt2\delta_{\mathrm{hon}}$) aborts or that the evaluation at $x$ differs from $P_{y,v}(x)$, the quantity bounded in Lemma 6.9.
--
--   These are the objects of Theorem 6.10.
--
--   **Formalization Note** As in Protocol 3, the prescribed uniform key $y$ is read off as $x_E$ of Protocol 2's run. The decoders' measurements may depend on the public data $(c_{\mathrm{msg}},\sigma,R,z)$, which Bob can copy to both. The challenge distribution is used for $m\ge1$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), §6.2 pp. 66–67, Definition 6.3 pp. 66–67, Protocol 5 p. 67, Lemma 6.9 p. 67

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_UEHonest

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms (Superop IsChannel)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr POVM)

noncomputable section

namespace FlexRigidity.Supplement

/-- **The multi-bit point function** `P_{y,v}` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §6.2, pp. 66–67): `P_{y,v}(x) = v` if `x = y`, and
`0^m` otherwise. -/
def pointFn {m : ℕ} (y v x : Fin m → Bool) : Fin m → Bool :=
  if x = y then v else fun _ => false

/-- **The challenge distribution of Definition 6.3** (step 3, p. 67): given the marked input `y`,
`X = y` with probability `1/2`, and otherwise `X` is uniform on `{0,1}^m \ {y}`. (Used for
`m ≥ 1`.) -/
def challengeP {m : ℕ} (y x : Fin m → Bool) : ℝ :=
  if x = y then 1 / 2 else 1 / (2 * ((2 : ℝ) ^ m - 1))

/-- **An attack in the copy-protection experiment after the protection protocol** (Definition 6.3,
steps 2–4, pp. 66–67, and Protocol 5, p. 67): Bob's splitting channel `Λ` from his register to
`D_1 ⊗ D_2`, which may depend on the public classical data `(c_msg, σ, R, z)`, and decoder `j`'s
measurement, which depends only on its own challenge `X^{(j)}` and the public data and outputs
`V^{(j)} ∈ {0,1}^m`. -/
structure CopyAttack (m s τ d : ℕ) where
  /-- dimension of decoder 1's register -/
  d1 : ℕ
  /-- dimension of decoder 2's register -/
  d2 : ℕ
  /-- Bob's splitting channel, given `c_msg, σ, R, z` -/
  Λ : (Fin m → Bool) → (Fin s → Bool) → (Fin τ → Fin m → Bool) → (Fin τ → Bool) →
    Superop (Fin d) (Fin d1 × Fin d2)
  /-- decoder 1's measurement, given `X^{(1)}, c_msg, σ, R, z`; outcome `V^{(1)}` -/
  F1 : (Fin m → Bool) → (Fin m → Bool) → (Fin s → Bool) → (Fin τ → Fin m → Bool) →
    (Fin τ → Bool) → (Fin m → Bool) → Matrix (Fin d1) (Fin d1) ℂ
  /-- decoder 2's measurement, given `X^{(2)}, c_msg, σ, R, z`; outcome `V^{(2)}` -/
  F2 : (Fin m → Bool) → (Fin m → Bool) → (Fin s → Bool) → (Fin τ → Fin m → Bool) →
    (Fin τ → Bool) → (Fin m → Bool) → Matrix (Fin d2) (Fin d2) ℂ

/-- The splitting maps are channels and the decoders' measurements are POVMs. -/
def CopyAttack.IsValid {m s τ d : ℕ} (att : CopyAttack m s τ d) : Prop :=
  (∀ c σ R z, IsChannel (att.Λ c σ R z)) ∧ (∀ x c σ R z, POVM (att.F1 x c σ R z)) ∧
    (∀ x c σ R z, POVM (att.F2 x c σ R z))

/-- **`Pr[Acc ∧ Bad_copy]`** for Protocol 5 (Definition 6.3 and Protocol 5, pp. 66–67). The
preparation of Protocol 3 runs with the key `k = y`; on `Acc ∧ (x_E, a_E) = (y, a)` its output is
`ρB (y, a)`. The marked value `v` is uniform, `c_msg = v ⊕ a`, `σ = syn(a)`, the hash matrix `R` is
uniform on binary `τ × m` matrices and `z = Ry`; the challenges `X^{(1)}, X^{(2)}` are drawn
independently from `challengeP y`;
`Bad_copy = (V^{(1)} = P_{y,v}(X^{(1)})) ∧ (V^{(2)} = P_{y,v}(X^{(2)}))`, false on abort.

**Formalization Note** As in `ueBlock`, the prescribed uniform key `y` is read off as `x_E` of
Protocol 2's run (Protocol 3's note, p. 63). -/
def copySucc {m s d : ℕ} (τ : ℕ) (ρB : (Fin m → Bool × Bool) → Matrix (Fin d) (Fin d) ℂ)
    (syn : (Fin m → Bool) → Fin s → Bool) (att : CopyAttack m s τ d) : ℝ :=
  ∑ xa : Fin m → Bool × Bool, ∑ v : Fin m → Bool, ∑ R : Fin τ → Fin m → Bool,
    ∑ w1 : Fin m → Bool, ∑ w2 : Fin m → Bool,
      let y : Fin m → Bool := fun j => (xa j).1
      let a : Fin m → Bool := fun j => (xa j).2
      (1 / 2 ^ m : ℝ) * (1 / 2 ^ (τ * m) : ℝ) * challengeP y w1 * challengeP y w2 *
        tr (Matrix.kronecker
              (att.F1 w1 (xorS v a) (syn a) R (matVecF2 R y) (pointFn y v w1))
              (att.F2 w2 (xorS v a) (syn a) R (matVecF2 R y) (pointFn y v w2)) *
            att.Λ (xorS v a) (syn a) R (matVecF2 R y) (ρB xa))

open Classical in
/-- **Honest pointwise failure of Protocol 5** (Lemma 6.9's quantity, p. 67): for the fixed point
function `P_{y,v}` and the fixed evaluation input `x`, the probability that the honest preparation of
Protocol 3 with key `y` (depolarizing noise `2√2 δ_hon`, p. 60) aborts or that the evaluation
returns a value different from `P_{y,v}(x)`. On acceptance, `R` is uniform; evaluation returns
`0^m` if `Rx ≠ Ry`, and otherwise measures Bob's stored halves of `E` in the bases `x`, corrects
with `σ = syn(a_E)` and returns the recovered string XOR `c_msg = v ⊕ a_E`. -/
def honestCopyFail (δ γ εtol : ℝ) (n τ : ℕ) {s : ℕ}
    (syn : (Fin (mLen γ n) → Bool) → Fin s → Bool)
    (dec : (Fin s → Bool) → (Fin (mLen γ n) → Bool) → (Fin (mLen γ n) → Bool))
    (y v x : Fin (mLen γ n) → Bool) : ℝ :=
  ∑ R : Fin τ → Fin (mLen γ n) → Bool, (1 / 2 ^ (τ * mLen γ n) : ℝ) *
    ∑ t : Fin n → RoundO Bool Bool Bool Bool,
      honestWeight δ γ y x t *
        (if h : honestAcc γ εtol t ∧ mLen γ n ≤ (genSet fun i => (t i).1).card then
          (if (if matVecF2 R x ≠ matVecF2 R y then (fun _ => false)
                else xorS (dec (syn (honestAE t h.2)) (honestBE t h.2)) (xorS v (honestAE t h.2)))
              = pointFn y v x then 0 else 1)
        else 1)

end FlexRigidity.Supplement


