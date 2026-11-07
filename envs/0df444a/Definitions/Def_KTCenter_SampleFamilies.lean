-- Prove2me | Definitions.Def_KTCenter_SampleFamilies
-- name    : KTCenter_SampleFamilies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:51.632184+00:00
-- url     : https://prove2.me/theorems/d4ef67bb-08dd-4dc8-9724-e4e06ae51e20
-- title:
--   The walk-based families: EnumerateLargeSamples (87) and EnumerateSmallSamples (93)
-- statement:
--   For the large blocks, (87) sets $R=|\mathcal B_\ell|$, $t_B=\lceil 512K^2|B|^2(\ell+R)/(\kappa^2Q_\ell)\rceil$, $T=\sum_B t_B$, and $H=m^2$ the smallest perfect square $\ge 2KN/\kappa$ with $N=|U'|$. A member of the **joint family** is obtained from one walk with $T$ states: in a fixed block order, each block receives the next $t_B$ states, mapped to candidates by $\psi_B$, and the distinct sampled candidates receive arbitrary allowed keys. With no large block the family has one empty member. For a small block $B$, (93) sets $\ell_0=\lceil\log_2(40nKN)\rceil$, $t_0=\lceil 160\kappa^{-2}\ell_0\rceil$, $m=2|B|$, $H=4|B|^2$, and a member of $G_B$ is a walk with $t_0$ states mapped by $\psi_B$, with arbitrary guessed keys.
--
--   **Formalization Note** The families are predicates on members; they depend on the instance and the block order only, never on a comparison assignment $p^*$.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §§6.2.2–6.2.3, eqs. (87), (93), pp.62–64 (PDF pp.64–66)

import Mathlib
import Definitions.Def_KTCenter_LP1
import Definitions.Def_KTCenter_MGGWalk

namespace KTCenter

namespace CostInstance

variable {K : ℕ} {C₀ C₁ : ℚ} (I : CostInstance K C₀ C₁) (ξ : ℚ)

/-- `N = |U′|`, p.37. -/
def Nres : ℕ := (I.Ures ξ).card

/-- `t_B = ⌈512K²|B|²(ℓ+R)/(κ²Q_ℓ)⌉`, `R = |ℬ_ℓ|`, eq. (87), p.62 (PDF p.64).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), §6.2.2. -/
def tLarge (B : Finset (Fin I.N)) : ℕ :=
  ⌈512 * (K : ℚ) ^ 2 * (B.card : ℚ) ^ 2 * ((I.ell : ℚ) + ((I.bLarge ξ).card : ℚ)) /
    (I.kappa ξ ^ 2 * (I.Qell ξ : ℚ))⌉₊

/-- `T = Σ_{B∈ℬ_ℓ} t_B`, eq. (87). -/
def Tlarge : ℕ := ∑ B ∈ I.bLarge ξ, I.tLarge ξ B

/-- `m` with `H = m²` the smallest perfect square `≥ 2KN/κ`, p.62.

**Formalization Note.** `sInf` of a nonempty set of naturals. `N ≥ 1` and `K ≥ 1` give `H ≥ 2`,
so `m ≥ 2` whenever a walk is used. -/
noncomputable def mLarge : ℕ :=
  sInf {m : ℕ | 2 * (K : ℚ) * (I.Nres ξ : ℚ) / I.kappa ξ ≤ (m : ℚ) ^ 2}

/-- `ℓ₀ = ⌈log₂(40nKN)⌉`, eq. (93), p.64 (PDF p.66). -/
def ell0 : ℕ := Nat.clog 2 (40 * I.n * K * I.Nres ξ)

/-- `t₀ = ⌈160κ⁻²ℓ₀⌉`, eq. (93). -/
def tSmall : ℕ := ⌈160 * (I.kappa ξ)⁻¹ ^ 2 * (I.ell0 ξ : ℚ)⌉₊

variable {I ξ}

/-- **The joint large-subset family**, EnumerateLargeSamples, p.62 (PDF p.64): `g` is in the family
when one walk with `T` states, cut into consecutive portions of lengths `t_B` in the subset order
`ord`, gives the sequence of every `B` through `ψ_B`, with `H = m²`; the guessed keys are arbitrary.

**Formalization Note.** The family is a function of the instance and `ord`, never of `p*`. With
`ℬ_ℓ = ∅` it is the one empty member ("use one empty family member and set A = 0"). The subset
order is "a fixed subset order" of p.62, so `ord` is a parameter. -/
def IsLargeMember (ord : Fin (I.bLarge ξ).card ≃ {B // B ∈ I.bLarge ξ})
    (g : I.LargeMember ξ) : Prop :=
  ∃ (z : ZMod (I.mLarge ξ) × ZMod (I.mLarge ξ)) (ls : Fin (I.Tlarge ξ - 1) → Fin 8),
    ∀ r : Fin (I.bLarge ξ).card,
      (g (ord r)).t = I.tLarge ξ (ord r).1 ∧
      ∀ j : Fin (g (ord r)).t,
        psiLookup (ord r).1 (I.mLarge ξ ^ 2)
          (stateIndex (I.mLarge ξ)
            (walkState (I.mLarge ξ) (I.Tlarge ξ) z ls
              ((∑ r' ∈ Finset.univ.filter (fun r' => r' < r), I.tLarge ξ (ord r').1) + j))) =
          some ((g (ord r)).seq j)

/-- **The family `G_B` of a small subset**, EnumerateSmallSamples, p.64 (PDF p.66): a walk with `t₀`
states on the graph with `m = 2|B|`, `H = 4|B|²`, mapped through `ψ_B`; the guessed keys are
arbitrary. -/
def IsSmallMember {B : Finset (Fin I.N)} (ξ : ℚ) (h : I.SampleGuess B) : Prop :=
  ∃ (z : ZMod (2 * B.card) × ZMod (2 * B.card)) (ls : Fin (I.tSmall ξ - 1) → Fin 8),
    h.t = I.tSmall ξ ∧
    ∀ j : Fin h.t,
      psiLookup B (4 * B.card ^ 2)
        (stateIndex (2 * B.card) (walkState (2 * B.card) (I.tSmall ξ) z ls j)) = some (h.seq j)

end CostInstance

end KTCenter


