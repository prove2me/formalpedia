-- Prove2me | Definitions.Def_DetDLP_FactorBase
-- name    : DetDLP_FactorBase
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T09:07:19.788573+00:00
-- url     : https://prove2.me/theorems/a6a3624f-4b7f-476f-abfe-18f2382aa47d
-- title:
--   Affine-Interval Factor Bases, Collision Potential $\Phi(S)$, and Decomposition Encodings
-- statement:
--   This definition module formalizes the Stage I affine-interval factor-base construction and collision potential for both prime-order elliptic curves $E(\mathbb{F}_p)$ and prime-field multiplicative groups $\mathbb{F}_p^*$.
--
--   It defines the block count $m = \max\{2, \lceil (\lceil \log_2(b+2) \rceil)^{1/4} \rceil\}$, the general-regime threshold parameters $q_* = \max\{4096 m, \lceil (16 g_{\mathrm{ord}})^{1/m} \rceil\}$, $T = \lceil p q_* / n \rceil$, and $q_{\mathrm{blk}} = nT/p$, together with the finite seed spaces `ECSeed` (two pairs $(\alpha_{i,\varepsilon}, \beta_{i,\varepsilon}) \in [1, p) \times [0, p)$ per block indexed by $y$-parity $\varepsilon$) and `FpSeed` (one pair per block). From the resulting factor-base subsets $F_1(S), \dots, F_m(S)$, it defines the representation counts $d_S(g)$, product size $W_S = \prod_i |F_i(S)|$, collision energy $C_S = \sum_g d_S(g)^2$, sumset/product-set supports, canonical binary encodings of factor bases and $2m$-term decompositions, and the collision potential
--
--   $$\Phi(S) = \frac{g_{\mathrm{ord}} C_S + 64(W_S - \mu)^2}{\mu^2}.$$
--
--   **Formalization Note** `ecPointFintype` constructs the canonical `Fintype` instance on Mathlib's `WeierstrassCurve.Affine.Point` over `ZMod p` via the equivalence with `Option {xy : ZMod p × ZMod p // Nonsingular xy.1 xy.2}`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3 (eqs. 3.1–3.2, Sections 3.1–3.2, pp. 11–13)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Canonical `Fintype` instance for affine points of a Weierstrass curve over `ZMod p`
(via equivalence with `Option {xy : ZMod p × ZMod p // E.toAffine.Nonsingular xy.1 xy.2}`). -/
@[implicit_reducible]
noncomputable def ecPointFintype {p : ℕ} [NeZero p] (E : WeierstrassCurve (ZMod p)) :
    Fintype E.toAffine.Point :=
  letI := Classical.decPred (fun xy : ZMod p × ZMod p => E.toAffine.Nonsingular xy.1 xy.2)
  Fintype.ofEquiv
    (Option {xy : ZMod p × ZMod p // E.toAffine.Nonsingular xy.1 xy.2})
    { toFun := fun
        | none => .zero
        | some ⟨⟨x, y⟩, h⟩ => .some x y h
      invFun := fun
        | .zero => none
        | .some x y h => some ⟨⟨x, y⟩, h⟩
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun P => by cases P <;> rfl }

/-- Stage I block count `m = max(2, ⌈(⌈log₂(b + 2)⌉)^{1/4}⌉)` (eq. 3.1). -/
noncomputable def blockCount (b : ℕ) : ℕ :=
  max 2 (Nat.ceil ((Nat.clog 2 (b + 2) : ℝ) ^ ((1 : ℝ) / 4)))

/-- General-regime parameter `q_* = max(4096 m, ⌈(16 g_ord)^{1/m}⌉)` (eq. 3.2). -/
noncomputable def qStar (m gord : ℕ) : ℕ :=
  max (4096 * m) (Nat.ceil ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))))

/-- Affine-hash threshold `T = ⌈p q_* / n⌉` (eq. 3.2). -/
noncomputable def hashThreshold (p n m gord : ℕ) : ℕ :=
  Nat.ceil (((p : ℝ) * (qStar m gord : ℝ)) / (n : ℝ))

/-- Expected per-block size `q_blk = n T / p` (Section 3.1). -/
noncomputable def qBlk (p n T : ℕ) : ℝ :=
  (n : ℝ) * (T : ℝ) / (p : ℝ)

/-- Affine-interval hash seed for the elliptic-curve case `E(F_p)`:
`2m` pairs `(α_{i,ε}, β_{i,ε}) ∈ [1, p) × [0, p)` encoded via `Fin (p - 1) × Fin p`
(where `α = a.val + 1 ∈ [1, p)`). -/
abbrev ECSeed (p m : ℕ) : Type :=
  Fin m → Bool → Fin (p - 1) × Fin p

/-- Affine-interval hash seed for the multiplicative case `F_p^*`:
`m` pairs `(α_i, β_i) ∈ [1, p) × [0, p)` encoded via `Fin (p - 1) × Fin p`
(where `α = a.val + 1 ∈ [1, p)`). -/
abbrev FpSeed (p m : ℕ) : Type :=
  Fin m → Fin (p - 1) × Fin p

/-- Boolean predicate for membership in the elliptic-curve affine-interval block `F_i(S)`. -/
def ecFactorMem {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)}
    {m : ℕ} (T : ℕ) (S : ECSeed p m) (i : Fin m) : E.toAffine.Point → Bool
  | .zero => false
  | .some x y _ =>
    let ε : Bool := decide (y.val % 2 = 1)
    let ab := S i ε
    let α : ℕ := ab.1.val + 1
    let β : ℕ := ab.2.val
    decide ((α * x.val + β) % p < T)

/-- Elliptic-curve affine-interval factor-base block `F_i(S) ⊆ E(F_p) \ {O}` (Section 3.1):
affine points `(x, y)` whose parity class `ε = (y mod 2)` satisfies
`(α_{i,ε} x + β_{i,ε}) mod p < T`. -/
noncomputable def ecFactorBlock {p : ℕ} [NeZero p] (E : WeierstrassCurve (ZMod p))
    {m : ℕ} (T : ℕ) (S : ECSeed p m) (i : Fin m) : Finset E.toAffine.Point :=
  letI := ecPointFintype E
  Finset.univ.filter fun P => ecFactorMem T S i P = true

/-- Boolean predicate for membership in the multiplicative affine-interval block `F_i(S)`. -/
def fpFactorMem {p : ℕ} [NeZero p] {m : ℕ} (T : ℕ) (S : FpSeed p m) (i : Fin m)
    (a : (ZMod p)ˣ) : Bool :=
  let ab := S i
  let α : ℕ := ab.1.val + 1
  let β : ℕ := ab.2.val
  decide ((α * (a : ZMod p).val + β) % p < T)

/-- Multiplicative-group affine-interval factor-base block `F_i(S) ⊆ F_p^*` (Section 3.1):
units `a ∈ F_p^*` satisfying `(α_i a + β_i) mod p < T`. -/
def fpFactorBlock {p : ℕ} [NeZero p] {m : ℕ} (T : ℕ) (S : FpSeed p m) (i : Fin m) :
    Finset (ZMod p)ˣ :=
  Finset.univ.filter fun a => fpFactorMem T S i a = true

/-- Sumset representation count `d_S(g) = |{(A₁,...,Aₘ) ∈ ∏ᵢ Fᵢ : ∑ᵢ Aᵢ = g}|`
in an additive finite abelian group. -/
def repCountAdd {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ}
    (F : Fin m → Finset G) (g : G) : ℕ :=
  ((Fintype.piFinset F).filter fun A => ∑ i : Fin m, A i = g).card

/-- Product-set representation count `d_S(g) = |{(A₁,...,Aₘ) ∈ ∏ᵢ Fᵢ : ∏ᵢ Aᵢ = g}|`
in a multiplicative finite abelian group. -/
def repCountMul {G : Type*} [CommGroup G] [DecidableEq G] {m : ℕ}
    (F : Fin m → Finset G) (g : G) : ℕ :=
  ((Fintype.piFinset F).filter fun A => ∏ i : Fin m, A i = g).card

/-- Product size `W_S = ∏_{i=1}^m |F_i|`. -/
def productSize {G : Type*} {m : ℕ} (F : Fin m → Finset G) : ℕ :=
  ∏ i : Fin m, (F i).card

/-- Collision energy `C_S = ∑_{g ∈ G} d_S(g)²` (additive group). -/
def collisionEnergyAdd {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
    (F : Fin m → Finset G) : ℕ :=
  ∑ g : G, (repCountAdd F g) ^ 2

/-- Collision energy `C_S = ∑_{g ∈ G} d_S(g)²` (multiplicative group). -/
def collisionEnergyMul {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
    (F : Fin m → Finset G) : ℕ :=
  ∑ g : G, (repCountMul F g) ^ 2

/-- Collision potential `Φ(S) = (g_ord · C_S + 64 (W_S - μ)²) / μ²` (Section 3.2, additive group). -/
noncomputable def collisionPotentialAdd {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} (μ : ℝ) (F : Fin m → Finset G) : ℝ :=
  ((Fintype.card G : ℝ) * (collisionEnergyAdd F : ℝ) +
    64 * ((productSize F : ℝ) - μ) ^ 2) / μ ^ 2

/-- Collision potential `Φ(S) = (g_ord · C_S + 64 (W_S - μ)²) / μ²` (Section 3.2, multiplicative group). -/
noncomputable def collisionPotentialMul {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} (μ : ℝ) (F : Fin m → Finset G) : ℝ :=
  ((Fintype.card G : ℝ) * (collisionEnergyMul F : ℝ) +
    64 * ((productSize F : ℝ) - μ) ^ 2) / μ ^ 2

/-- Sumset `F₁ + ... + Fₘ ⊆ G` (additive group). -/
def sumsetAdd {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ}
    (F : Fin m → Finset G) : Finset G :=
  (Fintype.piFinset F).image (fun A => ∑ i : Fin m, A i)

/-- Product set `F₁ · ... · Fₘ ⊆ G` (multiplicative group). -/
def prodsetMul {G : Type*} [CommGroup G] [DecidableEq G] {m : ℕ}
    (F : Fin m → Finset G) : Finset G :=
  (Fintype.piFinset F).image (fun A => ∏ i : Fin m, A i)

/-- Canonical binary encoding of a list of elliptic-curve points as `m` blocks of `(ι, x, y)` triples. -/
def encodeECFactorBlocks {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} {m : ℕ}
    (F : Fin m → List E.toAffine.Point) : List Bool :=
  Encoding.encodeList (Encoding.encodeList (fun P => encodeNatListBin (pointCoords P)))
    (List.ofFn F)

/-- Canonical binary encoding of `m` blocks of `F_p^*` elements as canonical residues in `[1, p)`. -/
def encodeFpFactorBlocks {p : ℕ} [NeZero p] {m : ℕ}
    (F : Fin m → List (ZMod p)ˣ) : List Bool :=
  Encoding.encodeList (Encoding.encodeList (fun a : (ZMod p)ˣ => countWord (a : ZMod p).val))
    (List.ofFn F)

/-- Canonical binary encoding of a `2m`-term elliptic-curve decomposition `(A₁, B₁, ..., Aₘ, Bₘ)`. -/
def encodeECDecomp {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} {m : ℕ}
    (A B : Fin m → E.toAffine.Point) : List Bool :=
  Encoding.encodeList (fun P => encodeNatListBin (pointCoords P))
    ((List.finRange m).flatMap fun i => [A i, B i])

/-- Canonical binary encoding of a `2m`-term multiplicative decomposition `(A₁, B₁, ..., Aₘ, Bₘ)`. -/
def encodeFpDecomp {p : ℕ} [NeZero p] {m : ℕ}
    (A B : Fin m → (ZMod p)ˣ) : List Bool :=
  encodeNatListBin ((List.finRange m).flatMap fun i => [(A i : ZMod p).val, (B i : ZMod p).val])

end DetDLP


