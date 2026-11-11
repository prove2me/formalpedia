-- Prove2me | Definitions.Def_HomIndGHW_RCR_Refinement
-- name    : HomIndGHW_RCR_Refinement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:00:55.430434+00:00
-- url     : https://prove2.me/theorems/447a1622-5f68-4299-a00a-0adfd2afb89a
-- title:
--   Flat tuples, atomic and similarity types, k-RCR (Definition 1.3), σ(≤k), pro-tuples MCT_k, k-proRCR (Definitions 1.6–1.7)
-- statement:
--   Fix $k\ge1$. The **flat tuples** $T_k(\mathcal A)$ are all concatenations $\bar t_1+\dots+\bar t_m$ of $1\le m\le k$ tuples of $\mathcal A$ (each in some relation; any order, repetitions allowed), as a set. For a flat tuple $t$, $\mathrm{atp}(t)=\{R\in\sigma: t\in R^{\mathcal A}\}$, and for flat tuples $s,t$ of lengths $\ell_s,\ell_t$
--   $$\mathrm{stp}(s,t)=\{(i,j)\mid 1\le i\le\ell_s,\ 1\le j\le\ell_t,\ s[i]=t[j]\}.$$
--   **$k$-RCR** (Definition 1.3) colours $T_k(\mathcal A)$ by $\kappa_0(t)=(\mathrm{atp}(t),\mathrm{stp}(t,t))$ and
--   $$\kappa_{i+1}(t)=\big(\kappa_i(t),\{\!\{(\mathrm{stp}(t,s),\kappa_i(s))\mid s\in T_k(\mathcal A),\ \mathrm{stp}(t,s)\neq\emptyset\}\!\}\big).$$
--   $\mathcal A\equiv_{k\text{-RCR}}\mathcal B$ when the stable colours occur equally often in $T_k(\mathcal A)$ and $T_k(\mathcal B)$; **$k$-RCR distinguishes** $\mathcal A,\mathcal B$ when this fails.
--
--   With a total order $\preceq_\sigma$ on $\sigma$, $\sigma(\le k)$ is the set of sequences $(R_1,\dots,R_m)$, $1\le m\le k$, $R_1\preceq_\sigma\dots\preceq_\sigma R_m$. The **pro-tuples** $\mathrm{MCT}_k(\mathcal A)$ are the $(\alpha;\bar t_1,\dots,\bar t_m)$ with $\alpha=(R_1,\dots,R_m)\in\sigma(\le k)$ and $\bar t_i\in R_i^{\mathcal A}$, with $\mathrm{Profile}=\alpha$ and $\mathrm{flat}=\bar t_1+\dots+\bar t_m$; $\mathrm{stp}(\Omega,\Psi)=\mathrm{stp}(\mathrm{flat}\,\Omega,\mathrm{flat}\,\Psi)$. **$k$-proRCR** (Definition 1.7) colours them by $\chi_0(\Omega)=(\mathrm{Profile}(\Omega),\mathrm{stp}(\Omega))$ and $\chi_{i+1}(\Omega)=(\chi_i(\Omega),\{\!\{(\mathrm{stp}(\Omega,\Psi),\chi_i(\Psi))\mid\Psi\in\mathrm{MCT}_k(\mathcal A),\mathrm{stp}(\Omega,\Psi)\ne\emptyset\}\!\})$, with $\equiv_{k\text{-proRCR}}$ defined in the same way.
--
--   $k$-RCR is the algorithm of the main theorem; $k$-proRCR is the profiled variant through which it is proved.
--
--   **Formalization Note.** Flat tuples are `List V`; `stp` keeps the paper's 1-based indices. A pro-tuple is stored as the pair $(\alpha,\bar t_1+\dots+\bar t_m)$ (the arities in $\alpha$ recover the $\bar t_i$), as §4 does. Colours are canonical values `RCRCol σ i`, `ProCol σ i` built from finite sets, lists of symbols and multisets, so they can be compared across structures with different domains. $\mathcal A\equiv_{k\text{-RCR}}\mathcal B$ is formalized in **all-rounds form**: for every round $i$ and every round-$i$ colour $c$, $|\{t\in T_k(\mathcal A)\mid\kappa_i(t)=c\}|=|\{t\in T_k(\mathcal B)\mid\kappa_i(t)=c\}|$. This is the stable-colour comparison: round $i+1$ colours contain round $i$ colours, and once both colourings are stable equal histograms at one round give equal histograms at the next. The same form is used for $\equiv_{k\text{-proRCR}}$.
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 5, Definition 1.3; pp. 6–7 and 18–19, Definitions 1.6–1.7 = 3.2–3.3 and σ(≤k) of Definition 1.13

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures

set_option autoImplicit false

namespace HomIndGHW.RCR

/-!
# Flat tuples, atomic and similarity types, k-RCR and k-proRCR

Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, *Homomorphism Indistinguishability Beyond
Graphs*, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), §1.2,
Definition 1.3 (p. 5); §1.3.1 and §3.2, Definitions 1.6–1.7 = 3.2–3.3, Definition 1.13's
`σ(≤k)` (pp. 6–7, 18–19).

* Flat tuples are `List V`; `T_k(A)` is a `Finset (List V)` (a set: a flat tuple obtained in two
  ways counts once).
* `stp(s, t) = {(i, j) | 1 ≤ i ≤ ℓ_s, 1 ≤ j ≤ ℓ_t, s[i] = t[j]}` with the paper's 1-based indices.
* A pro-tuple `(α; t̄₁, …, t̄_m) ∈ MCT_k(A)` is stored as the pair `(α, t̄₁ + ⋯ + t̄_m)` of its
  profile and its flattening, as §4 does (p. 30): the arities in `α` recover the `t̄_i`.
* **Colours are canonical values** shared by all structures over `σ`: round-`i` colours of k-RCR
  live in `RCRCol σ i`, built from sets of symbols, sets of index pairs and multisets only, so that
  they can be compared across two structures with different domains.
* **`≡_{k-RCR}` in all-rounds form.** `A ≡_{k-RCR} B` is read as: for every round `i` and every
  round-`i` colour `c`, `|{t ∈ T_k(A) | κ_i^A(t) = c}| = |{t ∈ T_k(B) | κ_i^B(t) = c}|`. This is the
  paper's "`E_k^A(c) = E_k^B(c)` for all stable colours `c`" (Definition 1.3): equal histograms at
  round `i + 1` give equal histograms at round `i` (the round-`i + 1` colour contains the round-`i`
  colour), and once both colourings are stable equal histograms at one round give equal histograms
  at the next (each stable class carries a single neighbourhood multiset). The same reading is used
  for `≡_{k-proRCR}`.
-/

open Structure Classical

variable {σ : Sig} {V : Type*} {W : Type*}

/-- `σ(≤k)`: the sequences `(R₁, …, R_m)` of symbols with `1 ≤ m ≤ k` and `R₁ ⪯σ ⋯ ⪯σ R_m`
(Definition 1.13, p. 9; p. 6). -/
def sigLe (σ : Sig) [LinearOrder σ.Sym] (k : ℕ) : Set (List σ.Sym) :=
  {α | 1 ≤ α.length ∧ α.length ≤ k ∧ α.Pairwise (· ≤ ·)}

/-- `t ∈ R^A` for a flat tuple `t` given as a list: `t` has length `ar(R)` and, read as a tuple,
lies in `R^A`. -/
def MemRel (A : Structure σ V) (R : σ.Sym) (t : List V) : Prop :=
  ∃ u ∈ A.rel R, List.ofFn u = t

/-- All pairs `(α, t̄₁ + ⋯ + t̄_m)` with `1 ≤ m ≤ k`, `α = (R₁, …, R_m)` and `t̄_i ∈ R_i^A`, in any
order of the symbols. -/
noncomputable def rawProTuples [Finite V] (A : Structure σ V) (k : ℕ) :
    Finset (List σ.Sym × List V) :=
  (Finset.Icc 1 k).biUnion fun m =>
    (Finset.univ : Finset (Fin m → CT A)).image fun cs =>
      (List.ofFn fun i => (cs i).sym, (List.ofFn fun i => (cs i).toList).flatten)

/-- `T_k(A)`, the **flat tuples** of `A` w.r.t. `k` (p. 5): every concatenation of `m` tuples of
`A` (each in some relation; any order, repetitions allowed) with `1 ≤ m ≤ k`. -/
noncomputable def flatTuples [Finite V] (A : Structure σ V) (k : ℕ) : Finset (List V) :=
  (rawProTuples A k).image Prod.snd

/-- `MCT_k(A)`, the **pro-tuples** (p. 6, p. 18): pairs `(α, t̄₁ + ⋯ + t̄_m)` with
`α = (R₁, …, R_m) ∈ σ(≤k)` and `t̄_i ∈ R_i^A`. -/
noncomputable def mct [Finite V] [LinearOrder σ.Sym] (A : Structure σ V) (k : ℕ) :
    Finset (List σ.Sym × List V) :=
  (rawProTuples A k).filter fun p => p.1.Pairwise (· ≤ ·)

/-- The **atomic type** `atp(t) = {R ∈ σ : t ∈ R^A}` of a flat tuple (p. 5). -/
noncomputable def atp (A : Structure σ V) (t : List V) : Finset σ.Sym :=
  Finset.univ.filter fun R => MemRel A R t

/-- The **similarity type** `stp(s, t) = {(i, j) | 1 ≤ i ≤ ℓ_s, 1 ≤ j ≤ ℓ_t, s[i] = t[j]}`
(p. 5; Definition 1.6), 1-based as in the paper. -/
noncomputable def stp (s t : List V) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 s.length ×ˢ Finset.Icc 1 t.length).filter fun p => s[p.1 - 1]? = t[p.2 - 1]?

/-- Round-`i` colours of k-RCR: `RCRCol σ 0 = 2^σ × 2^{ℕ×ℕ}` (atomic type, similarity type) and
`RCRCol σ (i+1) = RCRCol σ i × Multiset (2^{ℕ×ℕ} × RCRCol σ i)`. -/
def RCRCol (σ : Sig) : ℕ → Type
  | 0 => Finset σ.Sym × Finset (ℕ × ℕ)
  | i + 1 => RCRCol σ i × Multiset (Finset (ℕ × ℕ) × RCRCol σ i)

/-- The k-RCR colouring `κ_i^A` of `T_k(A)` (Definition 1.3, p. 5):
`κ_0(t) = (atp(t), stp(t, t))` and
`κ_{i+1}(t) = (κ_i(t), {{(stp(t, s), κ_i(s)) | s ∈ T_k(A), stp(t, s) ≠ ∅}})`. -/
noncomputable def kappa [Finite V] (A : Structure σ V) (k : ℕ) : (i : ℕ) → List V → RCRCol σ i
  | 0, t => (atp A t, stp t t)
  | i + 1, t => (kappa A k i t,
      (((flatTuples A k).filter fun s => stp t s ≠ ∅).val.map fun s => (stp t s, kappa A k i s)))

/-- `A ≡_{k-RCR} B` (Definition 1.3, all-rounds form; see the module note): for every round `i`
and every colour `c`, as many flat tuples of `A` as of `B` receive colour `c` at round `i`. -/
def RCREquiv [Finite V] [Finite W] (k : ℕ) (A : Structure σ V) (B : Structure σ W) : Prop :=
  ∀ (i : ℕ) (c : RCRCol σ i),
    ((flatTuples A k).filter fun t => kappa A k i t = c).card =
      ((flatTuples B k).filter fun t => kappa B k i t = c).card

/-- **k-RCR distinguishes `A` and `B`**: `A ≢_{k-RCR} B` (p. 5). -/
def RCRDistinguishes [Finite V] [Finite W] (k : ℕ) (A : Structure σ V) (B : Structure σ W) :
    Prop :=
  ¬ RCREquiv k A B

/-- Round-`i` colours of k-proRCR: `ProCol σ 0 = σ* × 2^{ℕ×ℕ}` (profile, similarity type) and
`ProCol σ (i+1) = ProCol σ i × Multiset (2^{ℕ×ℕ} × ProCol σ i)`. -/
def ProCol (σ : Sig) : ℕ → Type
  | 0 => List σ.Sym × Finset (ℕ × ℕ)
  | i + 1 => ProCol σ i × Multiset (Finset (ℕ × ℕ) × ProCol σ i)

/-- The k-proRCR colouring `χ_i^A` of `MCT_k(A)` (Definition 1.7 = 3.3, p. 7, p. 18), with
`stp(Ω, Ψ) = stp(flat(Ω), flat(Ψ))` (Definition 1.6 = 3.2):
`χ_0(Ω) = (Profile(Ω), stp(Ω))` and
`χ_{i+1}(Ω) = (χ_i(Ω), {{(stp(Ω, Ψ), χ_i(Ψ)) | Ψ ∈ MCT_k(A), stp(Ω, Ψ) ≠ ∅}})`. -/
noncomputable def chi [Finite V] [LinearOrder σ.Sym] (A : Structure σ V) (k : ℕ) :
    (i : ℕ) → List σ.Sym × List V → ProCol σ i
  | 0, Ω => (Ω.1, stp Ω.2 Ω.2)
  | i + 1, Ω => (chi A k i Ω,
      (((mct A k).filter fun Ψ => stp Ω.2 Ψ.2 ≠ ∅).val.map fun Ψ => (stp Ω.2 Ψ.2, chi A k i Ψ)))

/-- `A ≡_{k-proRCR} B` (Definition 1.7 = 3.3, all-rounds form as for k-RCR): for every round `i`
and every colour `c`, `|{Ω ∈ MCT_k(A) | χ_i^A(Ω) = c}| = |{Ω ∈ MCT_k(B) | χ_i^B(Ω) = c}|`. -/
def ProRCREquiv [Finite V] [Finite W] [LinearOrder σ.Sym] (k : ℕ) (A : Structure σ V)
    (B : Structure σ W) : Prop :=
  ∀ (i : ℕ) (c : ProCol σ i),
    ((mct A k).filter fun Ω => chi A k i Ω = c).card =
      ((mct B k).filter fun Ω => chi B k i Ω = c).card

/-- **k-proRCR distinguishes `A` and `B`**: `A ≢_{k-proRCR} B` (p. 8). -/
def ProRCRDistinguishes [Finite V] [Finite W] [LinearOrder σ.Sym] (k : ℕ) (A : Structure σ V)
    (B : Structure σ W) : Prop :=
  ¬ ProRCREquiv k A B

/-- The flattening of a pro-tuple is a flat tuple: `flat(MCT_k(A)) ⊆ T_k(A)` (structural). -/
theorem snd_mem_flatTuples_of_mem_mct [Finite V] [LinearOrder σ.Sym] {A : Structure σ V}
    {k : ℕ} {Ω : List σ.Sym × List V} (h : Ω ∈ mct A k) : Ω.2 ∈ flatTuples A k :=
  Finset.mem_image_of_mem _ (Finset.mem_filter.1 h).1

end HomIndGHW.RCR


