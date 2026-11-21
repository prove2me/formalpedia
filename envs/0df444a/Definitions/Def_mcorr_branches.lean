-- Prove2me | Definitions.Def_mcorr_branches
-- name    : mcorr_branches
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T23:30:59.231183+00:00
-- url     : https://prove2.me/theorems/35da2f96-57fc-464b-995a-2156d4e3d707
-- title:
--   Perturbed branches, transversality, holomorphic motion, and limit models
-- statement:
--   A univalent branch of $\mathbf{f}_0$ perturbs to a branch $\phi+c$ of $\mathbf{f}_c$; `perturbedComp` composes such perturbed branches. `gFun` ($g_c$) composes the first $\ell$ branches, `hFun` ($h_c$) the branches along the cycle, and `wFun` is $w(c)=h_c(g_c(c))-g_c(c)$. The family is transversal at $a$ (`TransversalAt`, Definition 3.1) if $w'(a)\ne0$; since the orbit-and-branch data is canonical, this is imposed for every representation. `IsMisiurewiczMotion` packages Lemma 3.2 (holomorphic motion of the Misiurewicz orbit, uniqueness of the bounded orbit of $\xi(c)$, the moved repelling cycle and its multiplier). `IsKoenigsFamily` packages Remark 4.1 (normalized Kœnigs linearization of $h_c$). `limitModelB` is the limit model $B_j(c)$ of eq. (4.2). `MultibrotJuliaSimilar` is the conclusion of Theorem 5.2: $J_a$ and $M_{p,q}$ asymptotically $\lambda(a)$-self-similar about $a$ with limit models $B_0(a)$ and $\mu_aB_0(a)$, where $\mu_a=g_a'(a)(\lambda(a)-1)/w'(a)\ne0$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Section 3 (eq. 3.1, 3.6, 3.9), Definition 3.1, Lemma 3.2, Remark 4.1, eq. 4.2, Theorem 5.2 (eq. 5.9, 5.10).

import Mathlib
import Definitions.Def_mcorr_family
import Definitions.Def_mcorr_misiurewicz
import Definitions.Def_mcorr_similarity

open Set Filter Topology Finset

namespace MultibrotCorr

/-- The perturbed composition of branches (paper, eq. (3.1) and (3.3)): starting from z, apply
successively phi start + c, phi (start+1) + c, ..., phi (start+len-1) + c. Each phi j is a univalent
branch of f_0, so phi j + c is the perturbed branch of f_c. -/
noncomputable def perturbedComp (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ)
    (start len : ℕ) (c : ℂ) : ℂ → ℂ :=
  fun z => (List.range len).foldl (fun acc i => φ (start + i) acc + c) z

/-- g_c: the composition of the first l perturbed branches, sending xi(c) to z_l(c)
(paper, eq. (3.6)). -/
noncomputable def gFun (e : UnicriticalExponent) (ℓ : ℕ) (φ : ℕ → ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  perturbedComp e φ 0 ℓ c

/-- h_c: the composition of the perturbed branches along the repelling cycle, with repelling
fixed point z_l(c) (paper, eq. (3.9)). -/
noncomputable def hFun (e : UnicriticalExponent) (ℓ n : ℕ) (φ : ℕ → ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  perturbedComp e φ ℓ n c

/-- w(c) = h_c(g_c(c)) - g_c(c), the function whose derivative at a defines transversality
(paper, Definition 3.1). -/
noncomputable def wFun (e : UnicriticalExponent) (ℓ n : ℕ) (φ : ℕ → ℂ → ℂ) : ℂ → ℂ :=
  fun c => hFun e ℓ n φ c (gFun e ℓ φ c c) - gFun e ℓ φ c c

/-- g_a'(a): the derivative at a of the composition of the first l branches along the base orbit,
the product of the branch derivatives (paper, Section 5, proof of Theorem 5.2). -/
noncomputable def gDerivBase (e : UnicriticalExponent) (ℓ : ℕ) (z : ℕ → ℂ) (a : ℂ) : ℂ :=
  ∏ i ∈ Finset.range ℓ, branchDerivFactor e a (z i) (z (i + 1))

/-- The transversality condition at a Misiurewicz parameter a: w'(a) != 0, where
w(c) = h_c(g_c(c)) - g_c(c) (paper, Definition 3.1). The orbit-and-branch data is canonical
(unique bounded orbit, unique branch germs), so the condition is imposed for every representation. -/
def TransversalAt (e : UnicriticalExponent) (a : ℂ) : Prop :=
  IsMisiurewicz e a ∧
  ∀ (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ),
    IsMisiurewiczOrbitData e a ℓ n z φ U → deriv (wFun e ℓ n φ) a ≠ 0

/-- The holomorphic motion of the Misiurewicz orbit (paper, Lemma 3.2): on a neighborhood W of a,
the moved orbit zz j c is holomorphic in c, starts at xi(c) = zz 0 c, is the unique bounded forward
orbit of xi(c), is eventually the repelling cycle alpha(c), and lam c is its multiplier. -/
def IsMisiurewiczMotion (e : UnicriticalExponent) (a : ℂ)
    (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
    (W : Set ℂ) (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ) : Prop :=
  IsOpen W ∧ a ∈ W ∧
  (∀ j, DifferentiableOn ℂ (zz j) W) ∧
  (∀ j, zz j a = z j) ∧
  (∀ c ∈ W, ∀ j, zz (j + 1) c ∈ unicriticalCorr e.p e.q c (zz j c)) ∧
  (∀ c ∈ W, ∀ w, IsForwardOrbit e c (zz 0 c) w → (∃ R, ∀ j, ‖w j‖ ≤ R) →
    w = fun j => zz j c) ∧
  (∀ c ∈ W, ∀ j ≥ ℓ, zz (j + n) c = zz j c) ∧
  (∀ c ∈ W, IsRepellingCycle e c n (fun j => zz (ℓ + j) c)) ∧
  (∀ c ∈ W, lam c = cycleMultiplier e c n (fun j => zz (ℓ + j) c)) ∧
  DifferentiableOn ℂ lam W ∧
  (∀ c ∈ W, perturbedComp e φ 0 ℓ c (zz 0 c) = zz ℓ c) ∧
  (∀ c ∈ W, Set.InjOn (perturbedComp e φ 0 ℓ c) W ∧
    DifferentiableOn ℂ (perturbedComp e φ 0 ℓ c) W) ∧
  (∀ c ∈ W, ∀ w ∈ W, perturbedComp e φ 0 ℓ c w = zz ℓ c → w = zz 0 c) ∧
  DifferentiableOn ℂ (fun p : ℂ × ℂ => perturbedComp e φ 0 ℓ p.1 p.2) (W ×ˢ W)

/-- The Koenigs linearization family (paper, Remark 4.1): for each c in W, phiK c is holomorphic
near zz l c, normalized by phiK c (zz l c) = 0 and derivative 1 there, and conjugates h_c to
multiplication by lam c on a small disk. -/
def IsKoenigsFamily (e : UnicriticalExponent) (ℓ n : ℕ) (φ : ℕ → ℂ → ℂ)
    (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ) (W : Set ℂ)
    (φK : ℂ → ℂ → ℂ) (φdom : ℂ → Set ℂ) : Prop :=
  ∀ c ∈ W, IsOpen (φdom c) ∧ zz ℓ c ∈ φdom c ∧ DifferentiableOn ℂ (φK c) (φdom c) ∧
    φK c (zz ℓ c) = 0 ∧ deriv (φK c) (zz ℓ c) = 1 ∧
    ∃ r : ℝ, 0 < r ∧ Metric.ball (zz ℓ c) r ⊆ φdom c ∧
      ∀ z ∈ Metric.ball (zz ℓ c) r,
        perturbedComp e φ ℓ n c z ∈ φdom c ∧
        lam c * φK c z = φK c (perturbedComp e φ ℓ n c z)

/-- The limit model B_j(c) of Theorem 4.1 (paper, eq. (4.2)): B_l(c) = phiK c '' (closure V ∩ K_c),
and B_j(c) is obtained by multiplying by the branch derivatives forward (j > l) or dividing
backward (j < l). -/
noncomputable def limitModelB (e : UnicriticalExponent) (ℓ : ℕ) (zz : ℕ → ℂ → ℂ)
    (φK : ℂ → ℂ → ℂ) (c : ℂ) (V : Set ℂ) (j : ℕ) : Set ℂ :=
  let Bl := φK c '' (closure V ∩ filledJulia e c)
  let factor : ℂ :=
    if j ≤ ℓ then
      (∏ i ∈ Finset.Icc (j + 1) ℓ, branchDerivFactor e c (zz (i - 1) c) (zz i c))⁻¹
    else
      ∏ i ∈ Finset.Icc (ℓ + 1) j, branchDerivFactor e c (zz (i - 1) c) (zz i c)
  (fun w => factor * w) '' Bl

/-- The conclusion of Theorem 5.2 (paper, Theorem B): both J_a and M_(p,q) are asymptotically
lam(a)-self-similar about a; the limit model of M_(p,q) is mu times the limit model B_0(a) of K_a,
with mu = g_a'(a) (lam(a) - 1) / w'(a) = g_a'(a) / u'(a) (paper, (5.9), (5.10)) nonzero. -/
def MultibrotJuliaSimilar (e : UnicriticalExponent) (a : ℂ) : Prop :=
  ∃ (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
    (W : Set ℂ) (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ)
    (φK : ℂ → ℂ → ℂ) (φdom : ℂ → Set ℂ) (V : Set ℂ) (μ : ℂ),
    IsMisiurewiczOrbitData e a ℓ n z φ U ∧
    IsMisiurewiczMotion e a ℓ n z φ U W zz lam ∧
    IsKoenigsFamily e ℓ n φ zz lam W φK φdom ∧
    IsOpen V ∧ zz ℓ a ∈ V ∧ closure V ⊆ φdom a ∧
    μ = gDerivBase e ℓ z a * (lam a - 1) / deriv (wFun e ℓ n φ) a ∧
    μ ≠ 0 ∧
    IsAsymptoticallySelfSimilar (juliaSet e a) a (lam a) (limitModelB e ℓ zz φK a V 0) ∧
    IsAsymptoticallySelfSimilar (multibrot e) a (lam a)
      ((fun w => μ * w) '' (limitModelB e ℓ zz φK a V 0))

end MultibrotCorr


