-- Prove2me | Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate
-- name    : JuHardCoreTransition_Mixing_GadgetRate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:15:48.508994+00:00
-- url     : https://prove2.me/theorems/11e0814c-68e0-4cef-ac22-488d76355c8b
-- title:
--   Random symmetric bipartite gadget, type weights, the rate function $\psi_t$ and the coefficient $C_d^{pm}$
-- statement:
--   **Gadget.** Fix $d\ge3$ and an even $N$. Choose $d$ independent uniform perfect matchings of the base labels $[N]$ (the colours); $P_0$ is this law (parallel edges allowed) and $\mathbb E_0$ its expectation. The gadget $G_v$ is the bipartite double cover of their union: vertices $i^+,i^-$ for $i\in[N]$, and each base edge $ij$ gives the edges $i^+j^-$ and $i^-j^+$.
--
--   **Types.** For an independent set $I$ of $G_v$ put $S=\{i:i^+\in I\}$, $T=\{i:i^-\in I\}$; label $i$ has state $a=(a^+,a^-)\in\Omega=\{00,10,01,11\}$. With $n_{10}=|S\setminus T|$, $n_{01}=|T\setminus S|$, $n_{11}=|S\cap T|$, $n_{00}=N-|S\cup T|$ the type is $\alpha_a=n_a/N$ (7.1), and
--   $$\rho=\alpha_{10}-\alpha_{01},\qquad b=(b_1,b_2)=(2(\alpha_{10}+\alpha_{01}),2\alpha_{11})\quad(7.2).$$
--   $Z_{G_v}(\alpha)=\sum_{I\in\mathcal I(G_v),\,\alpha(I)=\alpha}\lambda^{|I|}$ (7.3).
--
--   **Rate function.** $B_{aa'}=1$ iff $a^+a'^-=a^-a'^+=0$ (rows $(1,1,1,1),(1,1,0,0),(1,0,1,0),(1,0,0,0)$). $\mathcal P(\alpha)$ is the set of symmetric couplings of $\alpha$ with itself supported on $B$; $H(p)=-\sum p\log p$ with $0\log0=0$. On $\{\alpha\ge0,\ \mathcal P(\alpha)\neq\emptyset\}$,
--   $$\psi_t(\rho,b)=2(1-d)H(\alpha)+(b_1+2b_2)(\log\lambda_c(d)+t)+d\max_{P\in\mathcal P(\alpha)}H(P)\quad(7.4).$$
--   $\alpha_c=d^{-2}((d-1)^2,d-1,d-1,1)$, $b_c=(4(d-1)/d^2,2/d^2)$, $V_d(r)=A_dr^2-B_dr^4$ with $A_d=d(d-2)/(16(d-1))$, $B_d=d^4(d-2)/(768(d-1)^2)$, and $H_d$ the form $\frac{d^2}{2(d-2)}(y+2z)^2+\frac{d^2(d-2)}{2(d-1)(d^2-2d+2)}((d-2)z-y)^2$. $b^*_t(\rho)$ denotes a stable local maximiser of $b\mapsto\psi_t(\rho,b)$ near $b_c$.
--
--   **Second-moment coefficient.** $P_\alpha=\arg\max_{P\in\mathcal P(\alpha)}H(P)$, $T_\alpha(a,b)=P_\alpha(a,b)/\alpha_a$, $T_{\alpha,\perp}$ its restriction to $L^2_0(\alpha)$, $A_{\mathrm{col}}=\mathbf 1\mathbf 1^\top-I_d$, and
--   $$C_d^{pm}(\alpha,\beta)=\det\big(I-A_{\mathrm{col}}\otimes T_{\alpha,\perp}\otimes T_{\beta,\perp}\big)^{-1/2}\quad(8.18).$$
--
--   **Formalization Note.** States are `Fin 4` in the order $00,10,01,11$; `compat` is $B$, `compat2` is $B\otimes B$. Perfect matchings are fixed-point-free involutions of `Fin N`; `gadgetGraph M` is the double cover on `Fin N × Bool`; `typeCounts`, `typeWeight` ($Z_{G_v}(\alpha)$ for count vector $n$), `E0TypeWeight` and `E0TypeWeight2` average over all $d$-tuples of matchings (edge orders and orientations of Construction 6.1 do not affect these weights). Continuous types are parametrised by $(\rho,b)$ via `typeOf`/`coordsOf`; `psi d t ρ b` is (7.4) with `maxCouplingEntropy` an `sSup` over $\mathcal P(\alpha)$ (attained when nonempty), and `InRateDomain` is the domain of (7.4). `couplingSet` requires row sums $\xi$ (for a probability vector these are exactly the symmetric couplings). `entMaxCoupling` is the maximiser (zero if none), `transitionOf`/`transitionT` is $T_\xi$; $T_{\alpha,\perp}$ is represented on $\mathbb R^\Omega$ by $T_\alpha\Pi_\alpha$ with $\Pi_\alpha f=f-(\sum_b\alpha_bf(b))\mathbf 1$, which vanishes on constants and equals $T_\alpha$ on $L^2_0(\alpha)$, so `coeffPM` (a Kronecker-product determinant raised to $-1/2$) is exactly (8.18). `IsStableMaximizer d B W bstar`: for $(\rho,t)\in W$, `bstar t ρ` is a local maximiser of $\psi_t(\rho,\cdot)$ in $B$ and the only one in $B$.
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Construction 6.1; §7, (7.1)–(7.5), (7.8), (7.13), (7.19); §8.1, (8.9), (8.18), printed pp.37–84 / PDF pp.38–85

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing Matrix
open scoped Kronecker

/-!
# The random symmetric bipartite gadget, its type weights, the rate function `ψ_t`,
# the second-moment coefficient `C_d^{pm}`

Ju, Liu and Yin, *Fine-Grained Complexity Across the Computational Phase Transition*,
arXiv:2611.02702, pinned source.pdf dated 2026-11-02 (SHA256 6288a2d2…3678; arXiv version suffix
not supplied): Construction 6.1 (printed p.37 / PDF p.38), proof of Theorem 6.15 (printed p.53 /
PDF p.54), §7 equations (7.1)–(7.5), (7.8), (7.13), (7.19) (printed pp.56–61 / PDF pp.57–62),
§8.1 equations (8.9) and (8.18) (printed pp.80–84 / PDF pp.81–85).

**The gadget.** `N` base labels `Fin N`; a perfect matching of `Fin N` is a fixed-point-free
involution (`PerfMatch N`). For `d` matchings `M : Fin d → PerfMatch N` (the colours), the gadget
`gadgetGraph M` is the bipartite double cover of their union: vertices `(i, true) = i⁺` and
`(i, false) = i⁻`, and every base edge `ij` of some colour gives the edges `i⁺j⁻` and `i⁻j⁺`.
`P_0` is the law of `d` independent uniform perfect matchings (the uniform law on
`Fin d → PerfMatch N`); repeated base edges are allowed and do not affect independent sets.
(The edge orders and orientations of Construction 6.1 do not affect the gadget's type weights.)

**Types.** States `Ω = (00, 10, 01, 11)` are `Fin 4` in this order (`a = (a⁺, a⁻)`); label `i` of an
independent set `I` has state `(1[i⁺ ∈ I], 1[i⁻ ∈ I])`; `typeCounts I a = n_a`, and the type is
`α = n/N` (7.1). Continuous proportions are parametrised by `(ρ, b) = (ρ, (b₁, b₂))` through
`typeOf ρ b`, the inverse of (7.2): `ρ = α₁₀ − α₀₁`, `b₁ = 2(α₁₀ + α₀₁)`, `b₂ = 2α₁₁`.
`typeWeight M λ n = Z_{G_v}(α)` (7.3), `E0TypeWeight` its `P_0`-expectation, and
`E0TypeWeight2` the mixed second moment `E_0[Z(α) Z(β)]`.

**The rate function** (7.4): `ψ_t(ρ, b) = 2(1 − d) H(α) + (b₁ + 2b₂)(log λ_c(d) + t)
+ d max_{P ∈ P(α)} H(P)`, `H(p) = −∑ p log p` (`0 log 0 = 0`), where `P(α)` is the set of symmetric
couplings with marginal `α` supported on the compatibility relation `B`, `B_{aa'} = 1` iff
`a⁺a'⁻ = a⁻a'⁺ = 0`. Its domain is `α ≥ 0`, `P(α) ≠ ∅` (`InRateDomain`).

**Second-moment coefficient** (8.9), (8.18): `P_α` is the entropy-maximising element of `P(α)`,
`T_α(a,b) = P_α(a,b)/α_a`, and `C_d^{pm}(α,β) = det(I − A_col ⊗ T_{α,⊥} ⊗ T_{β,⊥})^{−1/2}` with
`A_col = 11ᵀ − I_d`. `T_{α,⊥}`, the restriction of `T_α` to `L²₀(α)`, is represented on all of
`ℝ^Ω` by `T_α Π_α` with `Π_α f = f − (∑_b α_b f(b))·1`: this operator is `0` on constants and agrees
with `T_α` on `L²₀(α)` (which `T_α` preserves), so the two determinants coincide.
-/

/-! ### Couplings and entropy (generic finite state space) -/

section Generic

variable {S : Type*} [Fintype S]

/-- Shannon entropy `H(p) = −∑_x p_x log p_x` with `0 log 0 = 0`. -/
noncomputable def entropy (p : S → ℝ) : ℝ := ∑ x, Real.negMulLog (p x)

/-- Entropy of a matrix viewed as a law on pairs, `H(P) = −∑_{a,b} P_{ab} log P_{ab}`. -/
noncomputable def entropy2 (P : S → S → ℝ) : ℝ := ∑ a, ∑ b, Real.negMulLog (P a b)

/-- `P(ξ)`: nonnegative symmetric matrices with row sums `ξ` (hence column sums `ξ`, total mass
`∑ ξ`; for a probability vector `ξ`, the symmetric couplings of `ξ` with itself) supported on the
compatibility relation `Bc`. -/
def couplingSet (Bc : S → S → Prop) (ξ : S → ℝ) : Set (S → S → ℝ) :=
  {P | (∀ a b, 0 ≤ P a b) ∧ (∀ a b, P a b = P b a) ∧ (∀ a, ∑ b, P a b = ξ a) ∧
    (∀ a b, ¬ Bc a b → P a b = 0)}

/-- `max_{P ∈ P(ξ)} H(P)` (attained on the compact set `P(ξ)` when it is nonempty). -/
noncomputable def maxCouplingEntropy (Bc : S → S → Prop) (ξ : S → ℝ) : ℝ :=
  sSup (entropy2 '' couplingSet Bc ξ)

/-- `P` maximises entropy over `P(ξ)`. -/
def IsEntropyMaxCoupling (Bc : S → S → Prop) (ξ : S → ℝ) (P : S → S → ℝ) : Prop :=
  P ∈ couplingSet Bc ξ ∧ ∀ Q ∈ couplingSet Bc ξ, entropy2 Q ≤ entropy2 P

/-- `P_ξ = argmax_{P ∈ P(ξ)} H(P)` (8.9) (unique by strict concavity of `H` when `P(ξ) ≠ ∅`);
`0` when no maximiser exists. -/
noncomputable def entMaxCoupling (Bc : S → S → Prop) (ξ : S → ℝ) : S → S → ℝ := by
  classical
  exact if h : ∃ P, IsEntropyMaxCoupling Bc ξ P then h.choose else 0

/-- `T_ξ(a, b) = P_ξ(a, b)/ξ_a` (8.9): the conditional law of the second endpoint state. -/
noncomputable def transitionOf (Bc : S → S → Prop) (ξ : S → ℝ) : Matrix S S ℝ :=
  fun a b => entMaxCoupling Bc ξ a b / ξ a

end Generic

/-! ### States, compatibility, types -/

/-- The occupation bit on the `+` side of a state in `Ω = (00, 10, 01, 11)`. -/
def plusBit (a : Fin 4) : Prop := a = 1 ∨ a = 3

/-- The occupation bit on the `−` side of a state. -/
def minusBit (a : Fin 4) : Prop := a = 2 ∨ a = 3

/-- The compatibility matrix `B` (7.21): two labels in states `a, a'` may be joined by a base edge
iff `a⁺ a'⁻ = a⁻ a'⁺ = 0`. Rows in order `00, 10, 01, 11`: `(1,1,1,1), (1,1,0,0), (1,0,1,0),
(1,0,0,0)`. -/
def compat (a a' : Fin 4) : Prop :=
  ¬ (plusBit a ∧ minusBit a') ∧ ¬ (minusBit a ∧ plusBit a')

/-- The two-replica compatibility `B ⊗ B` on `Ω²`. -/
def compat2 (x y : Fin 4 × Fin 4) : Prop := compat x.1 y.1 ∧ compat x.2 y.2

/-- The type `α = (α₀₀, α₁₀, α₀₁, α₁₁)` with coordinates `(ρ, b)` (inverse of (7.2)). -/
noncomputable def typeOf (ρ : ℝ) (b : ℝ × ℝ) : Fin 4 → ℝ :=
  ![1 - b.1 / 2 - b.2 / 2, b.1 / 4 + ρ / 2, b.1 / 4 - ρ / 2, b.2 / 2]

/-- The coordinates `(ρ, b) = (α₁₀ − α₀₁, (2(α₁₀ + α₀₁), 2α₁₁))` of a type (7.2). -/
noncomputable def coordsOf (α : Fin 4 → ℝ) : ℝ × (ℝ × ℝ) :=
  (α 1 - α 2, (2 * (α 1 + α 2), 2 * α 3))

/-- `(ρ, b)` lies in the domain of (7.4): `α ≥ 0` and `P(α) ≠ ∅`. -/
def InRateDomain (ρ : ℝ) (b : ℝ × ℝ) : Prop :=
  (∀ a, 0 ≤ typeOf ρ b a) ∧ (couplingSet compat (typeOf ρ b)).Nonempty

/-- **The rate function** (7.4), with `log λ = log λ_c(d) + t` (`t = δ̂`):
`ψ_t(ρ, b) = 2(1 − d) H(α) + (b₁ + 2b₂)(log λ_c(d) + t) + d max_{P ∈ P(α)} H(P)`. -/
noncomputable def psi (d : ℕ) (t ρ : ℝ) (b : ℝ × ℝ) : ℝ :=
  2 * (1 - (d : ℝ)) * entropy (typeOf ρ b) + (b.1 + 2 * b.2) * (Real.log (lamCrit d) + t) +
    (d : ℝ) * maxCouplingEntropy compat (typeOf ρ b)

/-- The critical type `α_c = d^{−2}((d−1)², d−1, d−1, 1)` (7.19). -/
noncomputable def alphaC (d : ℕ) : Fin 4 → ℝ :=
  ![((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 2, ((d : ℝ) - 1) / (d : ℝ) ^ 2, ((d : ℝ) - 1) / (d : ℝ) ^ 2,
    1 / (d : ℝ) ^ 2]

/-- `b_c = (4(d−1)/d², 2/d²)` (p.57). -/
noncomputable def bC (d : ℕ) : ℝ × ℝ := (4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2, 2 / (d : ℝ) ^ 2)

/-- `A_d = d(d−2)/(16(d−1))` (7.8). -/
noncomputable def coefA (d : ℕ) : ℝ := (d : ℝ) * ((d : ℝ) - 2) / (16 * ((d : ℝ) - 1))

/-- `B_d = d⁴(d−2)/(768(d−1)²)` (7.8). -/
noncomputable def coefB (d : ℕ) : ℝ := (d : ℝ) ^ 4 * ((d : ℝ) - 2) / (768 * ((d : ℝ) - 1) ^ 2)

/-- The quartic `V_d(r) = A_d r² − B_d r⁴` (7.8). -/
noncomputable def quarticV (d : ℕ) (r : ℝ) : ℝ := coefA d * r ^ 2 - coefB d * r ^ 4

/-- The symmetric bilinear form of `H_d` (7.13), whose quadratic form is
`d²/(2(d−2)) (y + 2z)² + d²(d−2)/(2(d−1)(d²−2d+2)) ((d−2)z − y)²`. -/
noncomputable def hessForm (d : ℕ) (u v : ℝ × ℝ) : ℝ :=
  (d : ℝ) ^ 2 / (2 * ((d : ℝ) - 2)) * (u.1 + 2 * u.2) * (v.1 + 2 * v.2) +
    (d : ℝ) ^ 2 * ((d : ℝ) - 2) / (2 * ((d : ℝ) - 1) * ((d : ℝ) ^ 2 - 2 * d + 2)) *
      (((d : ℝ) - 2) * u.2 - u.1) * (((d : ℝ) - 2) * v.2 - v.1)

/-- `bstar` is the **stable local maximiser** of `b ↦ ψ_t(ρ, b)` near `b_c` on the parameter set
`W` of pairs `(ρ, t)`: for `(ρ, t) ∈ W`, `bstar t ρ ∈ B` is a local maximiser of `ψ_t(ρ, ·)` and is
the only local maximiser of `ψ_t(ρ, ·)` lying in `B` (Lemma 7.8, p.61, notation `b*_t(ρ)`). -/
def IsStableMaximizer (d : ℕ) (B : Set (ℝ × ℝ)) (W : Set (ℝ × ℝ)) (bstar : ℝ → ℝ → ℝ × ℝ) :
    Prop :=
  ∀ ρ t : ℝ, (ρ, t) ∈ W → bstar t ρ ∈ B ∧ IsLocalMax (fun b => psi d t ρ b) (bstar t ρ) ∧
    ∀ b ∈ B, IsLocalMax (fun b' => psi d t ρ b') b → b = bstar t ρ

/-! ### The gadget and its type weights -/

/-- Perfect matchings of the base labels `Fin N`: fixed-point-free involutions. -/
abbrev PerfMatch (N : ℕ) := {σ : Equiv.Perm (Fin N) // ∀ i, σ i ≠ i ∧ σ (σ i) = i}

/-- The gadget `G_v` (Construction 6.1): the bipartite double cover of the union of the matchings
`M c`, on `Fin N × Bool` (`(i, true) = i⁺`, `(i, false) = i⁻`); each base edge `ij` of any colour
gives `i⁺j⁻` and `i⁻j⁺`. -/
def gadgetGraph {d N : ℕ} (M : Fin d → PerfMatch N) : SimpleGraph (Fin N × Bool) where
  Adj x y := x.2 ≠ y.2 ∧ ∃ c, (M c).1 x.1 = y.1
  symm := by
    constructor
    rintro x y ⟨h, c, hc⟩
    refine ⟨Ne.symm h, c, ?_⟩
    rw [← hc]
    exact ((M c).2 x.1).2
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The state `(a⁺, a⁻) ∈ Ω` of a pair of occupation bits, in the order `00, 10, 01, 11`. -/
def stateOfBits : Bool → Bool → Fin 4
  | false, false => 0
  | true, false => 1
  | false, true => 2
  | true, true => 3

/-- The state of base label `i` in the vertex set `I`: `(1[i⁺ ∈ I], 1[i⁻ ∈ I])`. -/
def labelState {N : ℕ} (I : Finset (Fin N × Bool)) (i : Fin N) : Fin 4 :=
  stateOfBits (decide ((i, true) ∈ I)) (decide ((i, false) ∈ I))

/-- The occupation counts `n_a` (7.1): the number of labels in state `a`. -/
def typeCounts {N : ℕ} (I : Finset (Fin N × Bool)) (a : Fin 4) : ℕ :=
  (Finset.univ.filter fun i => labelState I i = a).card

/-- The proportions `α_a = n_a / N` of a count vector. -/
noncomputable def propOf (N : ℕ) (n : Fin 4 → ℕ) : Fin 4 → ℝ := fun a => (n a : ℝ) / N

/-- `Z_{G_v}(α) = ∑_{I ∈ I(G_v), α(I) = α} λ^{|I|}` (7.3), for the integer type with counts `n`. -/
noncomputable def typeWeight {d N : ℕ} (M : Fin d → PerfMatch N) (lam : ℝ) (n : Fin 4 → ℕ) : ℝ := by
  classical
  exact ∑ I : Finset (Fin N × Bool),
    if (∀ x ∈ I, ∀ y ∈ I, ¬ (gadgetGraph M).Adj x y) ∧ typeCounts I = n then lam ^ I.card else 0

/-- `E_0 Z_{G_v}(α)`: the expectation of `typeWeight` under `P_0`, `d` independent uniform perfect
matchings of `Fin N`. -/
noncomputable def E0TypeWeight (d N : ℕ) (lam : ℝ) (n : Fin 4 → ℕ) : ℝ :=
  (∑ M : Fin d → PerfMatch N, typeWeight M lam n) / (Fintype.card (Fin d → PerfMatch N) : ℝ)

/-- `E_0[Z_{G_v}(α) Z_{G_v}(β)]` under `P_0`. -/
noncomputable def E0TypeWeight2 (d N : ℕ) (lam : ℝ) (n m : Fin 4 → ℕ) : ℝ :=
  (∑ M : Fin d → PerfMatch N, typeWeight M lam n * typeWeight M lam m) /
    (Fintype.card (Fin d → PerfMatch N) : ℝ)

/-! ### The second-moment coefficient -/

/-- `T_α` (8.9) for the one-replica compatibility `B`. -/
noncomputable def transitionT (α : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  transitionOf compat α

/-- `Π_α = I − 1 αᵀ`, the projection of functions on `Ω` onto `L²₀(α)` along the constants. -/
noncomputable def meanZeroProj (α : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => (if a = b then 1 else 0) - α b

/-- `T_{α,⊥}`, represented on `ℝ^Ω` as `T_α Π_α` (zero on constants, `T_α` on `L²₀(α)`). -/
noncomputable def transitionPerp (α : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  transitionT α * meanZeroProj α

/-- `A_col = 11ᵀ − I_d` (p.84). -/
def colourAdj (d : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => if i = j then 0 else 1

/-- **`C_d^{pm}(α, β) = det(I − A_col ⊗ T_{α,⊥} ⊗ T_{β,⊥})^{−1/2}`** (8.18). -/
noncomputable def coeffPM (d : ℕ) (α β : Fin 4 → ℝ) : ℝ :=
  (Matrix.det (1 - colourAdj d ⊗ₖ transitionPerp α ⊗ₖ transitionPerp β)) ^ (-(1 / 2 : ℝ))

end JuHardCoreTransition.Mixing


