-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Construction
-- name    : PostedPriceLimits_FullRevelation_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:34.296595+00:00
-- url     : https://prove2.me/theorems/b0d6bba9-dd07-4188-94dd-4738bc2a8549
-- title:
--   The §5 hard distribution: parameters, contexts, non-owner and owner valuations
-- statement:
--   All objects depend on the number of bidders $n$ (taken sufficiently large in §5).
--
--   **Parameters.** $\kappa=2^{20n}$ ranks; $\mathrm{val}(k)=\kappa^{\kappa^k}$ for $k\in[\kappa]$ and $\mathrm{val}(0)=0$; $\lambda=\mathrm{val}(\kappa)$; $m=n\lambda^{100}$ items; $\eta=m^{2n}$ names; $\varepsilon=\lambda^{-10}$. The items form $n$ consecutive blocks $Z_1,\dots,Z_n$ of size $\lambda^{100}$.
--
--   **Randomness.** A uniformly random owner permutation $\pi$ (bidder $i$ owns $Z_{\pi(i)}$); for each block $t$ an independent uniformly random injection $\tau_t:[n]\to[\eta]$ (the real names $\tau_t([n])$); name lists $N_{t,i}\subseteq[\eta]$ containing every real name and every other name independently with probability $1/m$. A **context** is $\gamma=(\ell,L)$ with $\varnothing\ne L\subseteq[\eta]$, $|L|\le n$, $\ell\in L$; $|\gamma|=|L|$ and $\gamma\subseteq L'$ means $L\subseteq L'$. Independently for every block, context and item, $\psi_{t,\gamma}(x)=k$ with probability $2/(\kappa\,\mathrm{val}(k))$ for $k\in[\kappa]$ and $0$ otherwise, and $\xi_{t,\gamma}(x)\sim\mathrm{Unif}[0,2]$; $\psi'_{t,\gamma}=\psi_{t,\gamma}\mathbf 1(\xi_{t,\gamma}\le1)$.
--
--   **Partitions and grid functions.** $\mathcal P_{t,L}$ partitions $Z_t$ by the label vectors $(\psi'_{t,\gamma}(x))_{\gamma\subseteq L}$; $\mathcal P_{t,(\ell,L)}=\mathcal P_{t,L\setminus\ell}$; $(\Pi_{t,L}f)(k,x)=\mathrm{Avg}[f(k,\cdot)\mid\mathcal P_{t,L}(x)]$. $\mathcal A_{t,L}$ is the set of all $A:[\kappa]\times Z_t\to\{0,\varepsilon,2\varepsilon,\dots,1\}$ with every $A(k,\cdot)$ $\mathcal P_{t,L}$-measurable, $\mathcal A_{t,(\ell,L)}=\mathcal A_{t,L\setminus\ell}$, and $A(0,\cdot)=0$.
--
--   **Non-owner valuation** (§5.1). The clause $u^{(t,\gamma,A)}$ has bias $u_0=|Z_t|(1-\mathrm{Avg}[A^2])+8\varepsilon|Z_t|(n-|\gamma|)$ (Avg over $[\kappa]\times Z_t$) and item value $2\,\mathrm{val}(\psi_{t,\gamma}(x))$ if $\xi_{t,\gamma}(x)\le1+A(\psi_{t,\gamma}(x),x)$, else $0$. With $\Gamma_{t,i}=\{(\tau_t(i),L):L\subseteq N_{t,i}\}$, $v_{t,i}(\varnothing)=0$ and $v_{t,i}(S)=\max_{\gamma\in\Gamma_{t,i}}\max_{A\in\mathcal A_{t,\gamma}}\{u^{(t,\gamma,A)}(S)+u_0^{(t,\gamma,A)}\}$ for $S\ne\varnothing$.
--
--   **Owner valuation** (§5.2). $Z_{t,k,I}=\bigcap_{\gamma\subseteq\tau_t(I)}\{x:\psi'_{t,\gamma}(x)\ge\varphi_{|\gamma|}(k)\}$ ($=Z_t$ for $I=\varnothing$), $\vartheta_{t,k,I}=\Pr[x\in Z_{t,k,I}]$. Conditionally on everything else, each item independently receives at most one owner rank, rank $k$ with probability $\mathbf 1(x\in Z_{t,k,[n]})/(\vartheta_{t,k,[n]}\mathrm{val}(k))$, giving the owner rank sets $Z_{t,k}$; $w_t$ is additive with $w_t(x)=\mathrm{val}(k)$ on $Z_{t,k}$ and $0$ elsewhere.
--
--   **Full instance** (§5.3). $v_i(S)=w_{\pi(i)}(S\cap Z_{\pi(i)})+\sum_{t\ne\pi(i)}v_{t,i}(S\cap Z_t)$.
--
--   **Formalization Note** All randomness is generated from independent $\mathrm{Unif}[0,1]$ labels (inversion for $\psi$, $\xi=2U$, name coin $U<1/m$, owner rank by consecutive intervals of lengths equal to the rank probabilities), a uniform family of injections $\tau_t$ and a uniform permutation $\pi$; this has exactly the joint law described above. $\vartheta_{t,k,I}$ is recorded for each item $x$ (it does not depend on $x$). Functions on $[\kappa]\times Z_t$ are functions $\mathbb N\to Z_t\to\mathbb R$ read on $[\kappa]\times Z_t$; grid functions vanish off $[\kappa]\times Z_t$, so $\mathcal A_{t,L}$ is in bijection with the source's set. `IsRealisation` singles out the points of the support of the law (every $\tau_t$ injective, $\pi$ a permutation, every label in $[0,1]$); pointwise statements are made for these.
--
--   The functions `hardWelfare` and `hardOptWelfare` compute respectively the welfare of an allocation and the maximum welfare over all feasible item assignments for this sampled instance; no bound is assumed.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), §5, pp.15–17 (PDF 16–18): parameters, §5.1 non-owner valuation, §5.2 owner valuation, §5.3 full instance; PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Prelim

open MeasureTheory

namespace PostedPriceLimits.FullRevelation

/-! ## The hard distribution of §5 (§§5–5.3)

All objects depend on the number of bidders `n`. Ranks are natural numbers, `[κ] = {1,…,κ}`;
functions "on `[κ] × Z_t`" are functions `ℕ → Fin b → ℝ` read on `[κ] × Z_t`. -/

/-- `κ = 2^{20n}`, the number of ranks. -/
def kappa (n : ℕ) : ℕ := 2 ^ (20 * n)

/-- `val(k) = κ^{κ^k}` for `k ∈ [κ]`, and `val(0) = 0`. -/
def val (n k : ℕ) : ℕ := if k = 0 then 0 else kappa n ^ (kappa n ^ k)

/-- `λ = val(κ)`. -/
def lam (n : ℕ) : ℕ := val n (kappa n)

/-- The block size `|Z_t| = λ^{100}`. -/
def blockSize (n : ℕ) : ℕ := lam n ^ 100

/-- `m = n λ^{100}`, the number of items. -/
def numItems (n : ℕ) : ℕ := n * blockSize n

/-- `η = m^{2n}`, the size of the name pool. -/
def poolSize (n : ℕ) : ℕ := numItems n ^ (2 * n)

/-- `ε = λ^{-10}`. -/
noncomputable def eps (n : ℕ) : ℝ := ((lam n : ℝ) ^ 10)⁻¹

/-- Item `j` of block `Z_t` as a global item: the blocks `Z_0, …, Z_{n-1}` are consecutive
runs of `λ^{100}` items in the item order. -/
def blockItem (n : ℕ) (t : Fin n) (j : Fin (blockSize n)) : Fin (numItems n) :=
  finProdFinEquiv (t, j)

/-- `S ∩ Z_t`, in the local coordinates of block `t`. -/
def localPart (n : ℕ) (S : Finset (Fin (numItems n))) (t : Fin n) : Finset (Fin (blockSize n)) :=
  Finset.univ.filter (fun j => blockItem n t j ∈ S)

/-- A context `γ = (ℓ, L)`: a name set `L ⊆ [η]` with `|L| ≤ n` and an element `ℓ ∈ L`
(so `L ≠ ∅`). -/
abbrev Ctx (n : ℕ) :=
  {c : Fin (poolSize n) × Finset (Fin (poolSize n)) // c.1 ∈ c.2 ∧ c.2.card ≤ n}

/-- Indices of the independent uniform labels: one for `ψ_{t,γ}(x)`, one for `ξ_{t,γ}(x)`, one
coin per (block, bidder, name) for the name lists, one per item for its owner rank. -/
abbrev LabelIdx (n : ℕ) :=
  (Fin n × Ctx n × Fin (blockSize n)) ⊕ (Fin n × Ctx n × Fin (blockSize n)) ⊕
    (Fin n × Fin n × Fin (poolSize n)) ⊕ (Fin n × Fin (blockSize n))

/-- A realisation of all the randomness: uniform labels, the name injections `τ_t` (as
`names t i = τ_t(i)`) and the owner permutation `π`. -/
abbrev Latent (n : ℕ) :=
  (LabelIdx n → ℝ) × (Fin n → Fin n → Fin (poolSize n)) × (Fin n → Fin n)

/-- The law of the randomness: independent `Unif[0,1]` labels, independent uniformly random
injections `τ_t : [n] → [η]` (one per block), and an independent uniformly random
permutation `π`. -/
noncomputable def latentLaw (n : ℕ) : Measure (Latent n) :=
  (Measure.pi (fun _ : LabelIdx n => unitUniform)).prod
    ((ProbabilityTheory.uniformOn
        {τ : Fin n → Fin n → Fin (poolSize n) | ∀ t, Function.Injective (τ t)}).prod
      (ProbabilityTheory.uniformOn {π : Fin n → Fin n | Function.Bijective π}))

variable {n : ℕ}

/-- `ω` is a genuine realisation of the construction (a point of the support of `latentLaw`):
every `τ_t` is an injection, `π` is a permutation, and every uniform label lies in `[0, 1]`. -/
def IsRealisation (ω : Latent n) : Prop :=
  (∀ t, Function.Injective (ω.2.1 t)) ∧ Function.Bijective ω.2.2 ∧ ∀ j, ω.1 j ∈ Set.Icc (0 : ℝ) 1

/-- The owner permutation: bidder `i` owns block `Z_{π(i)}`. -/
def perm (ω : Latent n) : Fin n → Fin n := ω.2.2

/-- The name `τ_t(i)` of bidder `i` in block `t`. -/
def names (ω : Latent n) (t : Fin n) : Fin n → Fin (poolSize n) := ω.2.1 t

/-- `Pr[ψ_{t,γ}(x) ≤ k]` mass on `[1, k]`: `∑_{j=1}^{k} 2/(κ val(j))`. -/
noncomputable def psiCumul (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, 2 / ((kappa n : ℝ) * val n j)

/-- `ψ_{t,γ}(x) ∈ {0, …, κ}`: equal to `k ∈ [κ]` with probability `2/(κ val(k))` and to `0`
with the remaining probability, obtained from its uniform label by inversion. -/
noncomputable def psi (ω : Latent n) (t : Fin n) (γ : Ctx n) (x : Fin (blockSize n)) : ℕ :=
  ∑ k ∈ rankRange (kappa n),
    if psiCumul n (k - 1) ≤ ω.1 (Sum.inl (t, γ, x)) ∧ ω.1 (Sum.inl (t, γ, x)) < psiCumul n k
    then k else 0

/-- `ξ_{t,γ}(x) ∼ Unif[0, 2]`. -/
noncomputable def xi (ω : Latent n) (t : Fin n) (γ : Ctx n) (x : Fin (blockSize n)) : ℝ :=
  2 * ω.1 (Sum.inr (Sum.inl (t, γ, x)))

/-- `ψ'_{t,γ}(x) = ψ_{t,γ}(x) 1(ξ_{t,γ}(x) ≤ 1)`. -/
noncomputable def psiPrime (ω : Latent n) (t : Fin n) (γ : Ctx n) (x : Fin (blockSize n)) : ℕ :=
  if xi ω t γ x ≤ 1 then psi ω t γ x else 0

/-- The name list `N_{t,i}`: every real name `τ_t([n])`, and every other name independently
with probability `1/m`. -/
noncomputable def nameList (ω : Latent n) (t i : Fin n) : Finset (Fin (poolSize n)) :=
  Finset.univ.image (names ω t) ∪
    Finset.univ.filter (fun a => ω.1 (Sum.inr (Sum.inr (Sum.inl (t, i, a)))) < 1 / (numItems n : ℝ))

/-- The name set `L ∖ {ℓ}` of a context `γ = (ℓ, L)` (`𝒫_{t,γ} = 𝒫_{t,L∖ℓ}`, `𝒜_{t,γ} = 𝒜_{t,L∖ℓ}`). -/
def ctxRest (γ : Ctx n) : Finset (Fin (poolSize n)) := γ.1.2.erase γ.1.1

/-- The part `𝒫_{t,L}(x)` of the partition `𝒫_{t,L}` of `Z_t` induced by
`{ψ'_{t,γ} : γ ⊆ L}`: the items with the same `ψ'_{t,γ}`-labels as `x` for every context
`γ ⊆ L`. -/
noncomputable def cell (ω : Latent n) (t : Fin n) (L : Finset (Fin (poolSize n)))
    (x : Fin (blockSize n)) : Finset (Fin (blockSize n)) :=
  Finset.univ.filter (fun y => ∀ γ : Ctx n, γ.1.2 ⊆ L → psiPrime ω t γ y = psiPrime ω t γ x)

/-- `f` is `𝒫_{t,L}`-measurable: constant on every part. -/
def IsCellMeasurable (ω : Latent n) (t : Fin n) (L : Finset (Fin (poolSize n)))
    (f : Fin (blockSize n) → ℝ) : Prop :=
  ∀ x y, y ∈ cell ω t L x → f y = f x

/-- `Π_{t,L} f`: `(Π_{t,L} f)(k, x) = Avg[f(k, ·) | 𝒫_{t,L}(x)]`. -/
noncomputable def proj (ω : Latent n) (t : Fin n) (L : Finset (Fin (poolSize n)))
    (f : ℕ → Fin (blockSize n) → ℝ) : ℕ → Fin (blockSize n) → ℝ :=
  fun k x => avg (cell ω t L x) (f k)

/-- `Avg[F]` for a function `F` on `[κ] × Z_t`: the uniform average over both coordinates. -/
noncomputable def avgRK (n : ℕ) (F : ℕ → Fin (blockSize n) → ℝ) : ℝ :=
  avg (rankRange (kappa n) ×ˢ (Finset.univ : Finset (Fin (blockSize n)))) (fun q => F q.1 q.2)

/-- `a` lies on the grid `{0, ε, 2ε, …, 1}`. -/
def IsGridValue (n : ℕ) (a : ℝ) : Prop :=
  ∃ j : ℕ, j ≤ lam n ^ 10 ∧ a = j * eps n

/-- `𝒜_{t,L}`: all functions `A : [κ] × Z_t → {0, ε, …, 1}` with `A(k, ·)` `𝒫_{t,L}`-measurable
for every `k ∈ [κ]`; outside `[κ] × Z_t` they are `0` (in particular `A(0, ·) = 0`). -/
def gridFns (ω : Latent n) (t : Fin n) (L : Finset (Fin (poolSize n))) :
    Set (ℕ → Fin (blockSize n) → ℝ) :=
  {A | (∀ k x, k ∉ rankRange (kappa n) → A k x = 0) ∧
    (∀ k ∈ rankRange (kappa n), ∀ x, IsGridValue n (A k x)) ∧
    (∀ k ∈ rankRange (kappa n), IsCellMeasurable ω t L (A k))}

/-- The bias `u₀^{(t,γ,A)} = |Z_t|(1 − Avg[A²]) + 8ε|Z_t|(n − |γ|)`. -/
noncomputable def clauseBias (γ : Ctx n) (A : ℕ → Fin (blockSize n) → ℝ) : ℝ :=
  (blockSize n : ℝ) * (1 - avgRK n (fun k x => A k x ^ 2)) +
    8 * eps n * (blockSize n : ℝ) * ((n : ℝ) - γ.1.2.card)

/-- The item value `u_x^{(t,γ,A)} = 2 val(ψ_{t,γ}(x))` if `ξ_{t,γ}(x) ≤ 1 + A(ψ_{t,γ}(x), x)`
and `0` otherwise. -/
noncomputable def clauseCoef (ω : Latent n) (t : Fin n) (γ : Ctx n)
    (A : ℕ → Fin (blockSize n) → ℝ) (x : Fin (blockSize n)) : ℝ :=
  if xi ω t γ x ≤ 1 + A (psi ω t γ x) x then 2 * (val n (psi ω t γ x) : ℝ) else 0

/-- `Γ_{t,i}`: the contexts `γ = (ℓ, L)` with `ℓ = τ_t(i)` and `L ⊆ N_{t,i}`. -/
noncomputable def ctxsOf (ω : Latent n) (t i : Fin n) : Finset (Ctx n) :=
  Finset.univ.filter (fun γ => γ.1.1 = names ω t i ∧ γ.1.2 ⊆ nameList ω t i)

/-- §5.1: the non-owner valuation `v_{t,i}` on `Z_t`: `v_{t,i}(∅) = 0` and, for `S ≠ ∅`, the
maximum of `u^{(t,γ,A)}(S) + u₀^{(t,γ,A)}` over `γ ∈ Γ_{t,i}` and `A ∈ 𝒜_{t,γ}` (a finite
nonempty family). -/
noncomputable def nonOwnerVal (ω : Latent n) (t i : Fin n) (S : Finset (Fin (blockSize n))) : ℝ :=
  if S = ∅ then 0 else
    sSup {r | ∃ γ ∈ ctxsOf ω t i, ∃ A ∈ gridFns ω t (ctxRest γ),
      r = ∑ x ∈ S, clauseCoef ω t γ A x + clauseBias γ A}

/-- `Z_{t,k,I} = ⋂_{γ ⊆ τ_t(I)} {x ∈ Z_t : ψ'_{t,γ}(x) ≥ φ_{|γ|}(k)}` (`= Z_t` for `I = ∅`). -/
noncomputable def zSet (ω : Latent n) (t : Fin n) (k : ℕ) (I : Finset (Fin n)) :
    Finset (Fin (blockSize n)) :=
  Finset.univ.filter (fun x => ∀ γ : Ctx n, γ.1.2 ⊆ I.image (names ω t) →
    phi (kappa n) γ.1.2.card k ≤ psiPrime ω t γ x)

/-- `ϑ_{t,k,I} = Pr[x ∈ Z_{t,k,I}]` for the item `x` of block `t`. -/
noncomputable def theta (n : ℕ) (t : Fin n) (k : ℕ) (I : Finset (Fin n)) (x : Fin (blockSize n)) :
    ℝ :=
  (latentLaw n).real {ω | x ∈ zSet ω t k I}

/-- Conditional probability `1(x ∈ Z_{t,k,[n]}) / (ϑ_{t,k,[n]} val(k))` that item `x` gets
owner rank `k`. -/
noncomputable def rankProb (ω : Latent n) (t : Fin n) (k : ℕ) (x : Fin (blockSize n)) : ℝ :=
  if x ∈ zSet ω t k Finset.univ then 1 / (theta n t k Finset.univ x * val n k) else 0

/-- `∑_{j=1}^{k}` of the rank probabilities of item `x`. -/
noncomputable def rankCumul (ω : Latent n) (t : Fin n) (k : ℕ) (x : Fin (blockSize n)) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, rankProb ω t j x

/-- The owner rank set `Z_{t,k}` (`k ∈ [κ]`; empty otherwise): conditionally on everything
else, each item independently gets at most one owner rank, rank `k` with probability
`1(x ∈ Z_{t,k,[n]}) / (ϑ_{t,k,[n]} val(k))` (realised by the item's uniform rank label). -/
noncomputable def ownerRankSet (ω : Latent n) (t : Fin n) (k : ℕ) : Finset (Fin (blockSize n)) :=
  if k ∈ rankRange (kappa n) then
    Finset.univ.filter (fun x => rankCumul ω t (k - 1) x ≤ ω.1 (Sum.inr (Sum.inr (Sum.inr (t, x)))) ∧
      ω.1 (Sum.inr (Sum.inr (Sum.inr (t, x)))) < rankCumul ω t k x)
  else ∅

/-- The owner's item value `w_t(x) = val(k)` for `x ∈ Z_{t,k}`, and `0` if `x` has no rank. -/
noncomputable def ownerItemVal (ω : Latent n) (t : Fin n) (x : Fin (blockSize n)) : ℝ :=
  ∑ k ∈ rankRange (kappa n), if x ∈ ownerRankSet ω t k then (val n k : ℝ) else 0

/-- §5.2: the additive owner valuation `w_t` on `Z_t`. -/
noncomputable def ownerVal (ω : Latent n) (t : Fin n) (S : Finset (Fin (blockSize n))) : ℝ :=
  ∑ x ∈ S, ownerItemVal ω t x

/-- §5.3: bidder `i`'s valuation
`v_i(S) = w_{π(i)}(S ∩ Z_{π(i)}) + ∑_{t ≠ π(i)} v_{t,i}(S ∩ Z_t)`. -/
noncomputable def bidderVal (ω : Latent n) (i : Fin n) (S : Finset (Fin (numItems n))) : ℝ :=
  ownerVal ω (perm ω i) (localPart n S (perm ω i)) +
    ∑ t ∈ Finset.univ.filter (fun t => t ≠ perm ω i), nonOwnerVal ω t i (localPart n S t)

/-- Social welfare of an allocation in the explicitly sampled §5 instance. -/
noncomputable def hardWelfare (ω : Latent n)
    (S : Fin n → Finset (Fin (numItems n))) : ℝ :=
  ∑ i, bidderVal ω i (S i)

/-- Optimal welfare of the §5 instance, a maximum over every feasible item assignment. -/
noncomputable def hardOptWelfare (ω : Latent n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun g : Fin (numItems n) → Option (Fin n) =>
      hardWelfare ω (fun i => Finset.univ.filter (fun x => g x = some i)))

end PostedPriceLimits.FullRevelation


