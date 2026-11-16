-- Prove2me | Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR
-- name    : FourWayStream_ARHM_Supplement_BlockXOR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:59:44.608286+00:00
-- url     : https://prove2.me/theorems/ec2c1bf8-2537-4a7c-aa04-f6ea41b01357
-- title:
--   Definitions 7.5, D.1 — Block Hidden XOR, its Fourier encoding, Distributional Hidden XOR on the multi-block graph
-- statement:
--   **Block Hidden XOR $\mathrm{BHX}_{w,r}$** ($w,r\ge1$). Alice receives independent uniform strings $X^i\in\{0,1\}^w$, $i\in[r]$; Bob receives independent uniform indices $J_i\in[w]$, independent of $X$. Alice sends one message (a density matrix on $\mathbb C^d$, private randomness averaged in, public coins allowed, no prior entanglement), and Bob, who sees all indices, must output
--   $$Z_J(X)=\bigoplus_{i=1}^rX^i_{J_i}.$$
--   The success probability averages over $X$, $J$ and the coins.
--
--   **Fourier encoding.** For an encoding $X\mapsto\rho_X$ let $I=[r]\times[w]$, $\chi_S(X)=(-1)^{\sum_{(i,j)\in S}X^i_j}$, $\hat\rho(S)=\mathbb E_X[\chi_S(X)\rho_X]$ for $S\subseteq I$, $S_J=\{(1,J_1),\dots,(r,J_r)\}$, $\rho_{J,b}=\mathbb E_X[\rho_X\mid Z_J(X)=b]$ and $\|A\|_{\mathrm{tr}}=\mathrm{Tr}\sqrt{A^\dagger A}$ (no factor $1/2$). The optimal prediction probability is the largest probability, over two-outcome measurements of the message, of outputting $Z_J(X)$ for a uniform $X$.
--
--   **Distributional Hidden XOR $\mathrm{DHX}_{w,t}$.** For $x\in\{0,1\}^w$ and a permutation $\sigma$ of $[w]$, $\mathrm{Block}(x,\sigma)$ has four layers of $2w$ vertices, in $w$ groups $\{a_j,b_j\}$: layer 1 to 2 sends group $j$ to group $\sigma(j)$ ($a$ to $a$, $b$ to $b$), layer 2 to 3 keeps the two edges of group $j$ parallel if $x_j=0$ and crosses them if $x_j=1$, layer 3 to 4 applies $\sigma^{-1}$. Chaining $t$ blocks (the last layer of one is the first of the next) gives $\mathrm{Multi\text{-}Block}(X,\Sigma)$ with $3t+1$ layers. With $X$ and $\Sigma$ uniform and independent, each edge is assigned to Alice or Bob independently with probability $1/2$; the players receive their edges as pairs of public vertex names, Alice sends one message, and Bob must output $z_G(1)=\bigoplus_{i=1}^tx^i_{\sigma^i(1)}$. Success averages over $(X,\Sigma)$, the split and the protocol's randomness.
--
--   These objects state Lemmas 7.6, 7.8, D.4 and Theorems 7.9, 7.10, D.5.
--
--   **Formalization Note** A vertex is (layer, group, side). Every vertex of layer $\ell+1$ has exactly one edge from layer $\ell$, so the fair split of the edges is a uniform function on these (layer, vertex) indices. Group $1$ is index $0$ of `Fin w`, which needs $w\ge1$.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), Definition 7.5, p.34; §7.3, pp.35–36; Appendix D.1, Definition D.1, p.46; §4.3, pp.16–17

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC

set_option autoImplicit false

/-!
# Block Hidden XOR (Definition 7.5), its Fourier encoding (§7.3), Distributional Hidden XOR
(Definition D.1)

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): Definition 7.5
(p.34), §7.3 (pp.35–36), Appendix D.1 (p.46), §4.3 (pp.16–17).

**Block Hidden XOR `BHX_{w,r}`.** Alice holds independent uniform strings `X^i ∈ {0,1}^w`,
`i ∈ [r]` (here `X : Fin r → Fin w → Bool`), Bob independent uniform indices `J_i ∈ [w]`
(`J : Fin r → Fin w`), independent of `X`. Bob must output `Z_J(X) = ⊕_i X^i_{J_i}`. A protocol has
public coins, Alice's message `msg c X` (a density matrix on `C^d`, private randomness averaged in, no
prior entanglement) and Bob's two-outcome POVM `povm c J` (he sees all indices jointly); its success
probability `succ` averages over `X`, `J` and the coins.

**Fourier encoding.** For an encoding `ρ : X ↦ ρ_X`, `I = [r] × [w]`,
`χ_S(X) = (−1)^{Σ_{(i,j) ∈ S} X^i_j}`, `ρ̂(S) = E_X[χ_S(X) ρ_X]`, `S_J = {(i, J_i)}`,
`ρ_{J,b} = E_X[ρ_X | Z_J(X) = b]`, and the trace norm `‖A‖_tr = Tr √(A†A)` (no factor `1/2`).
`optPredict ρ J` is the optimal probability, over two-outcome measurements of the message, of
predicting `Z_J(X)` for a uniform `X`.

**Distributional Hidden XOR `DHX_{w,t}`.** For `X = (x^1, …, x^t)` and permutations
`Σ = (σ^1, …, σ^t)` of `[w]`, the multi-block graph has `3t + 1` layers of `2w` vertices
`(ℓ, j, s)`: layer `ℓ`, group `j`, side `s` (`false = a`, `true = b`). Block `i` spans layers
`3i, …, 3i + 3`: from layer `3i` to `3i + 1` group `j` goes to group `σ^i(j)` (sides kept); from
`3i + 1` to `3i + 2` the two edges of group `j` are parallel if `x^i_j = 0` and crossed if
`x^i_j = 1`; from `3i + 2` to `3i + 3` group `j` goes to group `(σ^i)^{-1}(j)`. Consecutive blocks
share their boundary layer. Every vertex of layer `ℓ + 1` has exactly one edge from layer `ℓ`;
`dhxEdge X Σ ℓ (j, s)` is that edge, and the ownership `own : Fin (3t) × Fin w × Bool → Bool` (`true`
= Alice) assigns every edge of the graph independently and fairly. Players receive their edges as
pairs of public vertex names. The target is `z_G(1) = ⊕_i x^i_{σ^i(1)}` (group `1` is `0 : Fin w`).
Success averages over `X`, `Σ`, the ownership and the coins.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-! ### Block Hidden XOR -/

/-- `Z_J(X) = ⊕_{i} X^i_{J_i}`. -/
def hiddenXor {w r : ℕ} (X : Fin r → Fin w → Bool) (J : Fin r → Fin w) : Bool :=
  decide ((Finset.univ.filter (fun i => X i (J i) = true)).card % 2 = 1)

/-- A one-way protocol for `BHX_{w,r}` with `nR` public coin values. -/
structure BHXProtocol (w r nR : ℕ) where
  coin : Fin nR → ℝ
  d : ℕ
  msg : Fin nR → (Fin r → Fin w → Bool) → Matrix (Fin d) (Fin d) ℂ
  povm : Fin nR → (Fin r → Fin w) → Bool → Matrix (Fin d) (Fin d) ℂ

namespace BHXProtocol

variable {w r nR : ℕ}

/-- Coins form a probability vector, messages are density matrices, Bob measures with POVMs. -/
def Valid (P : BHXProtocol w r nR) : Prop :=
  ((∀ c, 0 ≤ P.coin c) ∧ ∑ c, P.coin c = 1) ∧ (∀ c X, IsDensityMatrix (P.msg c X)) ∧
    ∀ c J, IsPOVM (P.povm c J)

/-- Definition 7.5: the success probability, averaged over independent uniform `X`, independent
uniform `J`, and the coins. -/
def succ (P : BHXProtocol w r nR) : ℝ :=
  ∑ c, P.coin c * ∑ X : Fin r → Fin w → Bool, ∑ J : Fin r → Fin w,
    ((2 : ℝ) ^ (r * w))⁻¹ * ((w : ℝ) ^ r)⁻¹ * effectProb (P.povm c J (hiddenXor X J)) (P.msg c X)

end BHXProtocol

/-! ### The Fourier encoding -/

/-- `χ_S(X) = (−1)^{Σ_{(i,j) ∈ S} X^i_j}`. -/
def chiS {w r : ℕ} (S : Finset (Fin r × Fin w)) (X : Fin r → Fin w → Bool) : ℝ :=
  (-1) ^ (S.filter (fun p => X p.1 p.2 = true)).card

/-- `ρ̂(S) = E_X[χ_S(X) ρ_X]` for a uniform `X`. -/
def fourierCoeff {w r d : ℕ} (ρ : (Fin r → Fin w → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (S : Finset (Fin r × Fin w)) : Matrix (Fin d) (Fin d) ℂ :=
  ((2 : ℂ) ^ (r * w))⁻¹ • ∑ X, ((chiS S X : ℝ) : ℂ) • ρ X

/-- `S_J = {(1, J_1), …, (r, J_r)}`. -/
def blockSet {w r : ℕ} (J : Fin r → Fin w) : Finset (Fin r × Fin w) :=
  Finset.univ.image (fun i => (i, J i))

/-- `ρ_{J,b} = E_X[ρ_X | Z_J(X) = b]` for a uniform `X`. -/
def condState {w r d : ℕ} (ρ : (Fin r → Fin w → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (J : Fin r → Fin w) (b : Bool) : Matrix (Fin d) (Fin d) ℂ :=
  ((Finset.univ.filter (fun X => hiddenXor X J = b)).card : ℂ)⁻¹ •
    ∑ X ∈ Finset.univ.filter (fun X => hiddenXor X J = b), ρ X

/-- The trace norm `‖A‖_tr = Tr |A| = Tr √(A†A)` (no factor `1/2`). -/
def trNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (cfc Real.sqrt (Aᴴ * A)).trace.re

/-- The probability that the two-outcome measurement `E` of the message predicts `Z_J(X)`, for a
uniform `X`. -/
def predictProb {w r d : ℕ} (ρ : (Fin r → Fin w → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (J : Fin r → Fin w) (E : Bool → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ X, ((2 : ℝ) ^ (r * w))⁻¹ * effectProb (E (hiddenXor X J)) (ρ X)

/-- The optimal probability of predicting `Z_J(X)` from the message, over all two-outcome POVMs (a
supremum of a nonempty set bounded by `1` for density matrices). -/
def optPredict {w r d : ℕ} (ρ : (Fin r → Fin w → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (J : Fin r → Fin w) : ℝ :=
  ⨆ E : {E : Bool → Matrix (Fin d) (Fin d) ℂ // IsPOVM E}, predictProb ρ J E.1

/-! ### Distributional Hidden XOR -/

/-- The vertices of the multi-block graph with `t` blocks of width `w`: `(layer, group, side)`. -/
abbrev DHXV (w t : ℕ) := Fin (3 * t + 1) × Fin w × Bool

/-- The unique edge from layer `ℓ` into the vertex `(ℓ + 1, j, s)` of the multi-block graph
`Multi-Block(X, Σ)` (Appendix D.1, p.46; [AS23, Definitions 3.1–3.9]). With `i = ℓ / 3`:
phase `0` comes from `(ℓ, (σ^i)^{-1}(j), s)`; phase `1` from `(ℓ, j, s ⊕ x^i_j)`; phase `2` from
`(ℓ, σ^i(j), s)`. -/
def dhxEdge {w t : ℕ} (X : Fin t → Fin w → Bool) (sigmas : Fin t → Equiv.Perm (Fin w))
    (ℓ : Fin (3 * t)) (v : Fin w × Bool) : Sym2 (DHXV w t) :=
  let i : Fin t := ⟨ℓ.val / 3, by have := ℓ.isLt; omega⟩
  let lo : Fin (3 * t + 1) := ⟨ℓ.val, by have := ℓ.isLt; omega⟩
  let hi : Fin (3 * t + 1) := ⟨ℓ.val + 1, by have := ℓ.isLt; omega⟩
  let src : Fin w × Bool :=
    if ℓ.val % 3 = 0 then ((sigmas i).symm v.1, v.2)
    else if ℓ.val % 3 = 1 then (v.1, xor v.2 (X i v.1))
    else (sigmas i v.1, v.2)
  s((lo, src.1, src.2), (hi, v.1, v.2))

/-- The edges of `Multi-Block(X, Σ)` owned by `owner` under the ownership `own`. -/
def dhxShare {w t : ℕ} (X : Fin t → Fin w → Bool) (sigmas : Fin t → Equiv.Perm (Fin w))
    (own : Fin (3 * t) × Fin w × Bool → Bool) (owner : Bool) : Finset (Sym2 (DHXV w t)) :=
  (Finset.univ.filter (fun p : Fin (3 * t) × Fin w × Bool => own p = owner)).image
    (fun p => dhxEdge X sigmas p.1 p.2)

/-- `z_G(1) = ⊕_i x^i_{σ^i(1)}` (group `1` is `0 : Fin w`). -/
def dhxTarget {w t : ℕ} [NeZero w] (X : Fin t → Fin w → Bool) (sigmas : Fin t → Equiv.Perm (Fin w)) :
    Bool :=
  hiddenXor X (fun i => sigmas i 0)

/-- Definition D.1 (p.46): the success probability of a one-way protocol on edge shares for
`DHX_{w,t}`, averaged over uniform `X`, uniform `Σ`, the fair independent ownership of every edge
(`own = true`: Alice) and the coins. -/
def dhxSucc {w t nR : ℕ} [NeZero w] (P : ShareProtocol (DHXV w t) nR) : ℝ :=
  ∑ X : Fin t → Fin w → Bool, ∑ sigmas : Fin t → Equiv.Perm (Fin w),
    ∑ own : Fin (3 * t) × Fin w × Bool → Bool,
      ((Fintype.card (Fin t → Fin w → Bool) : ℝ))⁻¹ *
        ((Fintype.card (Fin t → Equiv.Perm (Fin w)) : ℝ))⁻¹ *
        ((Fintype.card (Fin (3 * t) × Fin w × Bool → Bool) : ℝ))⁻¹ *
        P.outProb (dhxShare X sigmas own true) (dhxShare X sigmas own false) (dhxTarget X sigmas)

end FourWayStream.ARHM.Supplement


