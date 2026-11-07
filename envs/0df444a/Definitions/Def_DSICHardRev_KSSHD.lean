-- Prove2me | Definitions.Def_DSICHardRev_KSSHD
-- name    : DSICHardRev_KSSHD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:43.876143+00:00
-- url     : https://prove2.me/theorems/35a71d8c-aec2-4422-891b-265c3f33fdfb
-- title:
--   Known-set simultaneous hard distributions ($(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD)
-- statement:
--   Fix $m\ge1$ items $M=[m]$. An $(\alpha,\eta,\lambda,C,\mathcal U)$-**KSSHD** is a distribution over combinatorial auctions with the following data and properties.
--
--   1. $\beta=m/\eta$ and $\kappa=m/(2\alpha)$ (integers), $\eta\ge1$, $\lambda\ge1$.
--   2. $C=(C_1,\dots,C_\lambda)$ with $C_\ell\subseteq[\beta]$ and $|C_\ell|=\alpha$.
--   3. $\mathcal U=\{u_x : x\in\{0,1,2\}^\lambda\}$ with monotone $u_x:2^{[\beta]}\to\mathbb Z_{\ge0}$, of one of three kinds:
--      - *GS or XOS* (every $u_x$ GS, resp. every $u_x$ XOS) with (i) $u_x(S)\le\min\{3\alpha,2|S|\}$, (ii) $u_x(C_\ell)\ge x_\ell\alpha$, (iii) $u_x(C_\ell)\le30\alpha/\eta^2$ if $x_\ell=0$; and, whenever $x_\ell=1$, $y_\ell=2$: $u_y(S)-u_x(S)\ge|S\cap C_\ell|-2|S\cap\bar C_\ell|-10\alpha/\eta^2$;
--      - *general*, with $C_\ell\cap C_{\ell'}\cap\bar C_{\ell''}\neq\emptyset$ whenever $\ell,\ell'\neq\ell''$, $u_x(S)=\max_\ell\{\alpha x_\ell\,\mathbb 1(S\supseteq C_\ell)\}$, and, whenever $x_\ell=1$, $y_\ell=2$: $u_y(S)-u_x(S)\ge\alpha\,\mathbb 1(S\supseteq C_\ell)-8|S\cap\bar C_\ell|$.
--   4. There are $n=\kappa\eta$ bidders in $\kappa$ groups $N_1,\dots,N_\kappa$ of size $\eta$. Independently for each group $k$ and index $\ell$, a uniformly random $j_{k,\ell}\in N_k$ gets $x_{j_{k,\ell},\ell}=1$ and the others of $N_k$ get $0$. Disjoint $A_1,\dots,A_\kappa,B\subseteq M$ with $|A_k|=\alpha$, $|B|=\beta-\alpha$ are uniformly random, $\vartheta\in[\lambda]$ is uniform, and uniformly random bijections $\varphi'_k:C_\vartheta\to A_k$, $\bar\varphi:\bar C_\vartheta\to B$ give $\varphi_k=\bar\varphi\cup\varphi'_k:[\beta]\to A_k\cup B$.
--   5. Bidder $i\in N_k$ has valuation $v_i(S)=u_{x_i}(\varphi_k^{-1}(S\cap(A_k\cup B)))$; it knows $(\varphi_k,x_i)$, and the referee knows $\varphi_1,\dots,\varphi_\kappa$. The bidder $i_k\in N_k$ with $x_{i_k,\vartheta}=1$ is the one with high value for $A_k$.
--
--   The definition also provides the optimal welfare $\max_{(T_1,\dots,T_n)}\sum_i v_i(T_i)$ over allocations.
--
--   KSSHDs are the hard distributions from which both the simultaneous lower bound and the DSIC reduction are derived.
--
--   **Formalization Note** Bidders are pairs $(k,i)$. A sample is $(j,\vartheta,\varphi)$ with $\varphi_k:[\beta]\hookrightarrow[m]$; it is valid when the $\varphi_k$ agree off $C_\vartheta$ and the sets $A_k=\varphi_k(C_\vartheta)$ are pairwise disjoint. The law of Properties (6)–(9) is the uniform law on valid samples (every choice of $A,B$ admits the same number of bijections), and expectations are uniform averages over valid samples. A field records that $\kappa\alpha+\beta-\alpha\le m$, so that the sets of Property (7) fit, and $m\ge1$. One branch (GS, XOS or general) is used for all $x$. $\lambda$ is written `lam`.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Definition 3.1, pp.11–12 (Properties (1)–(12), footnote 3); §2, p.7 (integrality); §3.2, p.14 (i_k)

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_DSICHardRev_ValuationClasses

namespace DSICHardRev

/-!
# Known-set simultaneous hard distributions (KSSHD)

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), Definition 3.1, pp.11–12 (Properties (1)–(12) and
footnote 3); the integrality convention of §2, p.7; valuations are monotone, §2.3, p.9; the bidder
`i_k ∈ N_k` with high value for `A_k`, §3.2, p.14.

**Formalization Note.**
* `m` is the number of (regular) items `Fin m`, with `m ≥ 1`. The parameters `α, η, λ` and the
  derived `β = m/η`, `κ = m/(2α)` are natural numbers (the paper assumes "all relevant quantities
  are integers", p.7); `β` and `κ` are fields constrained by `β · η = m` and `κ · (2α) = m`.
  `λ` is written `lam` (`λ` is a Lean keyword). `η ≥ 1`, `λ ≥ 1` (groups and `[λ]` are nonempty).
* `fits : κα + β ≤ m + α` says that `m` items suffice for the disjoint sets `A_1, …, A_κ, B` of
  sizes `α` and `β − α` (Property (7)); without it the distribution does not exist.
* `branch` records which alternative of Properties (3)–(4) the KSSHD uses: `gs` (every `u_x` is a
  GS valuation, Kelso–Crawford at all real prices) and `xos` (every `u_x` is XOS) use (3.a), (4.a);
  `gen` (general valuations) uses (3.b), (4.b). `x ∈ {0,1,2}^λ` is `Fin lam → Fin 3`; `ℤ₊` is `ℕ`;
  each `u_x` is monotone (a valuation). `C̄_ℓ` is the complement `[β] \ C_ℓ`.
* Properties (5)–(12) are the distribution. Bidders are pairs `(k, i) : Fin κ × Fin η` (group
  `N_k`, member `i`), so `n = κη`. A sample is `(j, ϑ, φ)`: `j k ℓ ∈ N_k` is the bidder of group
  `k` with `x_{(k,j k ℓ), ℓ} = 1` (Property (6)), `ϑ ∈ [λ]` (Property (8)), and
  `φ k : [β] ↪ [m]` is the bijection `φ_k = φ̄ ∪ φ'_k` onto `A_k ∪ B` (Property (9)). A sample is
  valid when all `φ_k` agree off `C_ϑ` (the common `φ̄`) and the sets `A_k = φ_k(C_ϑ)` are pairwise
  disjoint; then `B = φ_k(C̄_ϑ)` and Properties (7), (9), (10) hold. Sampling `x`, then `A, B`,
  `ϑ`, then the bijections uniformly as in Properties (6)–(9) is the same as sampling `j`
  uniformly and `(ϑ, φ)` uniformly among valid pairs, independently: every choice of `(A, B)`
  admits the same number `(α!)^κ (β − α)!` of bijections, for every `ϑ`. `expect H f` is the
  expectation over this uniform law on valid samples.
* The valuation of bidder `(k, i)` is `v(S) = u_{x}(φ_k^{-1}(S ∩ (A_k ∪ B)))` with
  `x_ℓ = 1(j k ℓ = i)` (Property (11)); `φ_k^{-1}(S ∩ (A_k ∪ B))` is the preimage of `S` under `φ_k`.
* `optWelfare v` is `max_{(T_1, …, T_n)} ∑_i v_i(T_i)` over allocations (pairwise disjoint bundles).
-/

/-- The three alternatives of Properties (3)–(4) of Definition 3.1. -/
inductive Branch
  /-- GS valuations, alternative (a). -/
  | gs
  /-- XOS valuations, alternative (a). -/
  | xos
  /-- General valuations, alternative (b). -/
  | gen
  deriving DecidableEq

/-- Property (3.a) of Definition 3.1: for all `x`, (i) `u_x(S) ≤ min{3α, 2|S|}`,
(ii) `u_x(C_ℓ) ≥ x_ℓ α`, (iii) `u_x(C_ℓ) ≤ 30α/η²` if `x_ℓ = 0`. -/
def Prop3a (α η : ℕ) {lam β : ℕ} (C : Fin lam → Finset (Fin β))
    (u : (Fin lam → Fin 3) → Finset (Fin β) → ℕ) : Prop :=
  ∀ x : Fin lam → Fin 3,
    (∀ S, (u x S : ℝ) ≤ min (3 * (α : ℝ)) (2 * (S.card : ℝ))) ∧
    (∀ l, ((x l : ℕ) : ℝ) * α ≤ (u x (C l) : ℝ)) ∧
    (∀ l, x l = 0 → (u x (C l) : ℝ) ≤ 30 * (α : ℝ) / (η : ℝ) ^ 2)

/-- Property (3.b) of Definition 3.1: (i) `C_ℓ ∩ C_ℓ' ∩ C̄_ℓ'' ≠ ∅` whenever `ℓ ≠ ℓ''` and
`ℓ' ≠ ℓ''`; (ii) `u_x(S) = max_ℓ {α x_ℓ · 1(S ⊇ C_ℓ)}`. -/
def Prop3b (α : ℕ) {lam β : ℕ} (C : Fin lam → Finset (Fin β))
    (u : (Fin lam → Fin 3) → Finset (Fin β) → ℕ) : Prop :=
  (∀ l l' l'' : Fin lam, l ≠ l'' → l' ≠ l'' → (C l ∩ C l' ∩ (C l'')ᶜ).Nonempty) ∧
    ∀ (x : Fin lam → Fin 3) (S : Finset (Fin β)),
      u x S = Finset.univ.sup fun l => α * (x l : ℕ) * (if C l ⊆ S then 1 else 0)

/-- Property (4.a) of Definition 3.1: if `x_ℓ = 1` and `y_ℓ = 2`, then
`u_y(S) − u_x(S) ≥ |S ∩ C_ℓ| − 2|S ∩ C̄_ℓ| − 10α/η²`. -/
def Prop4a (α η : ℕ) {lam β : ℕ} (C : Fin lam → Finset (Fin β))
    (u : (Fin lam → Fin 3) → Finset (Fin β) → ℕ) : Prop :=
  ∀ (S : Finset (Fin β)) (x y : Fin lam → Fin 3) (l : Fin lam), x l = 1 → y l = 2 →
    ((S ∩ C l).card : ℝ) - 2 * ((S ∩ (C l)ᶜ).card : ℝ) - 10 * (α : ℝ) / (η : ℝ) ^ 2 ≤
      (u y S : ℝ) - (u x S : ℝ)

/-- Property (4.b) of Definition 3.1: if `x_ℓ = 1` and `y_ℓ = 2`, then
`u_y(S) − u_x(S) ≥ α · 1(S ⊇ C_ℓ) − 8|S ∩ C̄_ℓ|`. -/
def Prop4b (α : ℕ) {lam β : ℕ} (C : Fin lam → Finset (Fin β))
    (u : (Fin lam → Fin 3) → Finset (Fin β) → ℕ) : Prop :=
  ∀ (S : Finset (Fin β)) (x y : Fin lam → Fin 3) (l : Fin lam), x l = 1 → y l = 2 →
    (α : ℝ) * (if C l ⊆ S then 1 else 0) - 8 * ((S ∩ (C l)ᶜ).card : ℝ) ≤
      (u y S : ℝ) - (u x S : ℝ)

/-- Properties (3)–(4) of Definition 3.1 for the chosen branch, including the valuation class. -/
def BranchProps (b : Branch) (α η : ℕ) {lam β : ℕ} (C : Fin lam → Finset (Fin β))
    (u : (Fin lam → Fin 3) → Finset (Fin β) → ℕ) : Prop :=
  match b with
  | .gs => (∀ x, KelsoCrawford.OneSided.GrossSubstitutesOn (fun S => (u x S : ℝ)) Set.univ) ∧
      Prop3a α η C u ∧ Prop4a α η C u
  | .xos => (∀ x, IsXOS (fun S => (u x S : ℝ))) ∧ Prop3a α η C u ∧ Prop4a α η C u
  | .gen => Prop3b α C u ∧ Prop4b α C u

/-- An `(α, η, λ, C, U)`-KSSHD on `m` regular items (Definition 3.1, Properties (1)–(4)); the
distribution of Properties (5)–(12) is `KSSHD.expect`. -/
structure KSSHD (m : ℕ) where
  /-- The parameter `α` (size of each `C_ℓ` and of each `A_k`). -/
  α : ℕ
  /-- The parameter `η` (group size). -/
  η : ℕ
  /-- The parameter `λ` (number of sets `C_ℓ`). -/
  lam : ℕ
  /-- `β = m/η`. -/
  β : ℕ
  /-- `κ = m/(2α)` (number of groups). -/
  κ : ℕ
  /-- Which alternative of Properties (3)–(4) is used. -/
  branch : Branch
  /-- The sets `C = (C_1, …, C_λ)`, `C_ℓ ⊆ [β]`. -/
  C : Fin lam → Finset (Fin β)
  /-- The valuations `U = {u_x : x ∈ {0,1,2}^λ}`, `u_x : 2^[β] → ℤ₊`. -/
  u : (Fin lam → Fin 3) → Finset (Fin β) → ℕ
  m_pos : 0 < m
  η_pos : 0 < η
  lam_pos : 0 < lam
  /-- Property (1): `β = m/η`. -/
  β_mul : β * η = m
  /-- Property (1): `κ = m/(2α)`. -/
  κ_mul : κ * (2 * α) = m
  /-- The sets `A_1, …, A_κ, B` of Property (7) fit into the `m` items. -/
  fits : κ * α + β ≤ m + α
  /-- Property (2): `|C_ℓ| = α`. -/
  card_C : ∀ l, (C l).card = α
  /-- Each `u_x` is a valuation, hence monotone (p.9). -/
  mono : ∀ x, Monotone (u x)
  /-- Properties (3)–(4) for the chosen branch. -/
  props : BranchProps branch α η C u

namespace KSSHD

variable {m : ℕ} (H : KSSHD m)

/-- The bidders: `(k, i)` is member `i` of group `N_k` (Property (5)). -/
abbrev Bidder := Fin H.κ × Fin H.η

/-- A sample `(j, ϑ, φ)`: `j k ℓ` is the bidder of `N_k` with `x_{·,ℓ} = 1` (Property (6)), `ϑ`
the index of Property (8), `φ k = φ_k : [β] ↪ [m]` (Property (9)). -/
abbrev Sample := (Fin H.κ → Fin H.lam → Fin H.η) × Fin H.lam × (Fin H.κ → (Fin H.β ↪ Fin m))

/-- Validity of a sample: the `φ_k` agree off `C_ϑ` (they share `φ̄`), and the sets
`A_k = φ_k(C_ϑ)` are pairwise disjoint. -/
def Valid (ω : H.Sample) : Prop :=
  (∀ k k' b, b ∉ H.C ω.2.1 → ω.2.2 k b = ω.2.2 k' b) ∧
    ∀ k k', k ≠ k' → Disjoint ((H.C ω.2.1).map (ω.2.2 k)) ((H.C ω.2.1).map (ω.2.2 k'))

/-- `A_k = φ_k(C_ϑ)`. -/
def A (ω : H.Sample) (k : Fin H.κ) : Finset (Fin m) := (H.C ω.2.1).map (ω.2.2 k)

/-- `A_{k,ℓ} = φ_k(C_ℓ)` (Property (10)). -/
def Akl (ω : H.Sample) (k : Fin H.κ) (l : Fin H.lam) : Finset (Fin m) := (H.C l).map (ω.2.2 k)

/-- The input vector `x_{(k,i)} ∈ {0,1}^λ`: `x_ℓ = 1` iff `j k ℓ = i` (Property (6)). -/
def xvec (ω : H.Sample) (b : H.Bidder) : Fin H.lam → Fin 3 :=
  fun l => if ω.1 b.1 l = b.2 then 1 else 0

/-- The valuation of bidder `(k, i)` (Property (11)): `v(S) = u_x(φ_k^{-1}(S ∩ (A_k ∪ B)))`. -/
def val (ω : H.Sample) (b : H.Bidder) (S : Finset (Fin m)) : ℝ :=
  (H.u (H.xvec ω b) (Finset.univ.filter fun c => ω.2.2 b.1 c ∈ S) : ℝ)

/-- `i_k ∈ N_k`: the bidder of group `k` with high value for `A_k` (`x_{i_k, ϑ} = 1`). -/
def ik (ω : H.Sample) (k : Fin H.κ) : H.Bidder := (k, ω.1 k ω.2.1)

open Classical in
/-- The valid samples. -/
noncomputable def support : Finset H.Sample := Finset.univ.filter H.Valid

/-- The expectation over the KSSHD: the uniform average over valid samples (Properties (5)–(9)). -/
noncomputable def expect (f : H.Sample → ℝ) : ℝ :=
  (∑ ω ∈ H.support, f ω) / (H.support.card : ℝ)

end KSSHD

/-- Allocations of the items `ι` to the bidders `N`: pairwise disjoint bundles. -/
def Alloc (N ι : Type) : Type := {S : N → Finset ι // Pairwise fun a b => Disjoint (S a) (S b)}

/-- The empty allocation. -/
def Alloc.empty (N ι : Type) : Alloc N ι :=
  ⟨fun _ => ∅, fun _ _ _ => Finset.disjoint_empty_left _⟩

open Classical in
noncomputable instance (N ι : Type) [Fintype N] [Fintype ι] : Fintype (Alloc N ι) :=
  Subtype.fintype _

/-- The optimal welfare `max_{(T_1, …, T_n)} ∑_i v_i(T_i)` over allocations. -/
noncomputable def optWelfare {N ι : Type} [Fintype N] [Fintype ι] (v : N → Finset ι → ℝ) : ℝ :=
  (Finset.univ : Finset (Alloc N ι)).sup' ⟨Alloc.empty N ι, Finset.mem_univ _⟩
    fun T => ∑ i, v i (T.1 i)

end DSICHardRev


