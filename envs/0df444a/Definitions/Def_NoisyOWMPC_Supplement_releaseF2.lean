-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_releaseF2
-- name    : NoisyOWMPC_Supplement_releaseF2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:05:21.547991+00:00
-- url     : https://prove2.me/theorems/8da1d171-fa55-40eb-a207-26e8f32b634b
-- title:
--   Construction F.2: the verifiable release test from a nontrivial core
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ have a nontrivial core. The **channel constants** are two core inputs $a_0, a_1$ forming a nontrivial pair, with output distributions $\mu_x = C(\cdot \mid a_x)$, the set $\mathcal Y_0 = \mathrm{supp}(\mu_0) \cup \mathrm{supp}(\mu_1)$, the posterior vectors $q_y(x) = \mu_x(y)/(\mu_0(y) + \mu_1(y))$, a bit $x^*$ such that $\mu_{x^*}$ has two distinct posterior vectors in its support, and a posterior vector $q^*$ occurring in the support of $\mu_{x^*}$; the **preserved bit** is $\beta(y) = \mathbf 1[q_y = q^*]$ on $\mathcal Y_0$ and $0$ elsewhere.
--
--   With $M$ rows, $t = 4M^{16}$, $n_{\mathrm{rel}} = Mt$, $a_t = \lceil t^{11/20}\rceil$, $b_t = \lceil t^{2/5}\rceil$, $P_t = 4\lceil t^{9/20}/4\rceil$, a signed row $\theta = ((x_s, \epsilon_s))_{s \in [t]}$ has nominal inputs $x_s \in \{0,1\}$ and signs $\epsilon_s \in \{-1,1\}$, and is **balanced** if it has $t/4$ copies of every pair. For a query row $w \in \mathcal Y^t$, $\mathrm{Check}_\theta(w) = 1$ iff $\mu_{x_s}(w_s) > 0$ at every position and $|n_{x,y}(w) - N_x \mu_x(y)| \le a_t$ for all $x \in \{0,1\}$, $y \in \mathcal Y_0$; the score is $B_\theta(w) = \sum_s \epsilon_s \beta(w_s)$ and the **row test** is
--   $$
--   h_\theta(w) = \mathrm{Check}_\theta(w)\, \mathrm{Mod}_{P_t}(B_\theta(w)).
--   $$
--   The row labels are $A$ if $h_\theta(w) = 1$, $R$ if $\mathrm{Check}_\theta(w) = 1$ and $B_\theta(w)$ is at distance at least $b_t$ from the accepting scores, and $F$ otherwise.
--
--   **Construction F.2.**
--
--   1. $\mathrm{Gen_{rel}}$: $M$ independent uniform balanced signed rows; $\mathrm{Word_{rel}}(\Theta)$: the inputs $a_{x_{j,s}}$ in row order; $Q_\Theta(w) = \mathbf 1[\sum_j h_{\theta_j}(w_j) > M/2]$.
--   2. $\mathrm{Valid_{rel}}(\Theta) = 1$ iff $\Theta$ consists of $M$ balanced signed rows of length $t$.
--   3. $\mathrm{SampleSt_{rel}}$: sample the honest experiment $(\Theta^0, D)$, record $H = Q_{\Theta^0}(D)$, the signed weights and labels of the rows, and candidate rows $T_j(\zeta) = \pi_{j,\zeta}\theta^0_j$ for uniform permutations preserving the equal-$D_j$ position sets; $\mathrm{Recons_{rel}}(st, \sigma)$ takes $\theta_j = T_j(\gamma^{\mathrm{rel}}_j(\sigma))$.
--   4. $\mathrm{Rec_{rel}}(st, w)$: the empty list if $H = 1$; otherwise the lists $\{\zeta : h_{T_j(\zeta)}(w_j) = 1\}$ for the rows labelled $R$, each discarded if larger than $M^{16}$, decoded by the expander $G_{\mathrm{rel}}$ ($M$ layers, $\ell = M^{16}$, $G = \lceil M^{2/5}\rceil$).
--
--   It instantiates the verifiable release test of Construction E.8 in Theorem E.10.
--
--   **Formalization Note** Secret states range over all $M$-tuples of signed rows, so that $\mathrm{Valid_{rel}}$ is meaningful; $\mathrm{Gen_{rel}}$ is uniform on the valid ones. The support and bit predicates use the true channel; the count centres of the check use the public rational upper approximations of the channel probabilities (§5 conventions). The constants $(a_0, a_1, x^*, q^* = q_{y^*})$ are parameters, with the conditions above collected in a separate predicate.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §F.1 Channel constants, pp.67–68; Parameters and row test, (F.1)–(F.3), p.68; Construction F.2, pp.68–69

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_Verifiable
import Definitions.Def_NoisyOWMPC_Supplement_NontrivialCore
import Definitions.Def_NoisyOWMPC_Supplement_periodic
import Definitions.Def_NoisyOWMPC_releaseTest

namespace NoisyOWMPC.Supplement

open LaconicBarrier KarpLiptonOM

variable {X Yc : Type} [Fintype X] [Fintype Yc]

/-- The output distribution `μ_x = C(· | a_x)` of the designated input `a_x`, `x ∈ {0,1}` (Ishai, Lu,
Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), §F.1 Channel constants, p.67); the bit
`0` is `false`. -/
def muF (C : DMC X Yc) (a : Bool → X) (x : Bool) (y : Yc) : ℝ := C.P (a x) y

/-- `y ∈ Y₀ = supp(μ₀) ∪ supp(μ₁)` (p.67). -/
def InY0 (C : DMC X Yc) (a : Bool → X) (y : Yc) : Prop := 0 < muF C a false y ∨ 0 < muF C a true y

/-- The posterior vector `q_y(x) = μ_x(y)/(μ₀(y) + μ₁(y))` of a uniform input `x ∈ {0,1}` given the
output `y ∈ Y₀` (p.67). -/
noncomputable def postF (C : DMC X Yc) (a : Bool → X) (y : Yc) (x : Bool) : ℝ :=
  muF C a x y / (muF C a false y + muF C a true y)

/-- The **channel constants of Construction F.2** (p.67): `a₀ = a(0)`, `a₁ = a(1)` are inputs of a
core of `C` with distinct output distributions and intersecting supports ("Since the core of `C` is
nontrivial, it has two inputs `a₀, a₁ ∈ X` with distinct output distributions and intersecting
supports"); `μ_{x*}` has two distinct posterior vectors in its support ("Some `μ_{x*}` has two
distinct posterior vectors in its support"); and `q* = q_{y*}` is a posterior vector occurring in
the support of `μ_{x*}` ("Fix a posterior vector `q*` occurring in the support of `μ_{x*}`"). -/
def IsF2Constants (C : DMC X Yc) (a : Bool → X) (xstar : Bool) (ystar : Yc) : Prop :=
  (∃ S : Finset X, IsCoreSet C S ∧ a false ∈ S ∧ a true ∈ S) ∧
  IsNontrivialPair C (a false) (a true) ∧
  0 < muF C a xstar ystar ∧ ∃ y, 0 < muF C a xstar y ∧ postF C a y ≠ postF C a ystar

open Classical in
/-- The **preserved bit** `β(y) = 1[q_y = q*]` for `y ∈ Y₀`, extended by zero on `Y ∖ Y₀` (pp.67–68). -/
noncomputable def betaF (C : DMC X Yc) (a : Bool → X) (ystar : Yc) (y : Yc) : Bool :=
  decide (InY0 C a y ∧ postF C a y = postF C a ystar)

/-- The row length `t = 4M¹⁶` (p.68). -/
def tF (M : ℕ → ℕ) (lam : ℕ) : ℕ := 4 * M lam ^ 16

/-- The channel-input length `n_rel = Mt = 4M¹⁷` (p.68). -/
def nF (M : ℕ → ℕ) (lam : ℕ) : ℕ := M lam * tF M lam

open Classical in
/-- A signed row `θ = ((x_s, ε_s))_{s ∈ [t]}` with nominal inputs `x_s ∈ {0,1}` and signs
`ε_s ∈ {−1, 1}` (`+1` is `true`) is **balanced** (p.68: "is balanced if it has `t/4` copies of every
input/sign pair"); `t/4 = M¹⁶`. -/
def BalancedF (Mv : ℕ) {t : ℕ} (θ : Fin t → Bool × Bool) : Prop :=
  ∀ x e, (Finset.univ.filter fun s => θ s = (x, e)).card = Mv ^ 16

open Classical in
/-- The **consistency check** `Check_θ(w)` (p.68, (F.1)): `μ_{x_s}(w_s) > 0` at every position, and
`|n_{x,y}(w) − N_x μ_x(y)| ≤ a_t` for all `x ∈ {0,1}`, `y ∈ Y₀`, with `N_x = |{s : x_s = x}|`,
`n_{x,y}(w) = |{s : x_s = x, w_s = y}|`, `a_t = ⌈t^{11/20}⌉`, and `μ_x(y)` in the comparison replaced
by its public rational upper approximation `apx`. -/
def checkF (C : DMC X Yc) (a : Bool → X) (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (lam : ℕ)
    {t : ℕ} (θ : Fin t → Bool × Bool) (w : Fin t → Yc) : Prop :=
  (∀ s, 0 < muF C a (θ s).1 (w s)) ∧
  ∀ x y, InY0 C a y → |((Finset.univ.filter fun s => (θ s).1 = x ∧ w s = y).card : ℚ) -
    ((Finset.univ.filter fun s => (θ s).1 = x).card : ℚ) * apx lam 0 (a x) y| ≤ (aTol t : ℚ)

/-- The **signed score** `B_θ(w) = ∑_{s=1}^t ε_s β(w_s)` (p.68). -/
noncomputable def scoreF (C : DMC X Yc) (a : Bool → X) (ystar : Yc) {t : ℕ}
    (θ : Fin t → Bool × Bool) (w : Fin t → Yc) : ℤ :=
  ∑ s, (if (θ s).2 then (1 : ℤ) else -1) * (if betaF C a ystar (w s) then 1 else 0)

open Classical in
/-- The **row test** `h_θ(w) = Check_θ(w) Mod_{P_t}(B_θ(w))` (F.2), `P_t = 4⌈t^{9/20}/4⌉`; it is
defined for unbalanced rows too, with their actual counts (p.68). -/
noncomputable def rowF (C : DMC X Yc) (a : Bool → X) (ystar : Yc)
    (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (lam : ℕ) {t : ℕ} (θ : Fin t → Bool × Bool)
    (w : Fin t → Yc) : Bool :=
  decide (checkF C a apx lam θ w) && modP (pPer t) (scoreF C a ystar θ w)

open Classical in
/-- The **row labels** (F.3), `0 = A`, `1 = R`, `2 = F`: `A` if `h_θ(w) = 1`; `R` if
`Check_θ(w) = 1` and `dist(B_θ(w), A_t) ≥ b_t` with `A_t = {z : Mod_{P_t}(z) = 1}`, `b_t = ⌈t^{2/5}⌉`;
`F` otherwise (p.68). -/
noncomputable def labelF (C : DMC X Yc) (a : Bool → X) (ystar : Yc)
    (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (lam : ℕ) {t : ℕ} (θ : Fin t → Bool × Bool)
    (w : Fin t → Yc) : Fin 3 :=
  if rowF C a ystar apx lam θ w = true then 0
  else if checkF C a apx lam θ w ∧ FarFrom (pPer t) true (bMar t) (scoreF C a ystar θ w) then 1
  else 2

open Classical in
/-- The **release test** `Q_Θ(w) = 1[∑_{j=1}^M h_{θ_j}(w_j) > M/2]` (Construction F.2, p.68), `w_j`
the `j`th length-`t` row of the query. -/
noncomputable def testF (C : DMC X Yc) (a : Bool → X) (ystar : Yc)
    (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (M : ℕ → ℕ) (lam : ℕ)
    (Θ : Fin (M lam) → Fin (tF M lam) → Bool × Bool) (w : Fin (nF M lam) → Yc) : Bool :=
  decide (M lam < 2 * (Finset.univ.filter fun j : Fin (M lam) =>
    rowF C a ystar apx lam (Θ j) (rowOf w j) = true).card)

/-- The release expander `G_rel`: the layered `(M ℓ_rel, G, L_out)`-list-recoverable graph of the
family `Gr` with `M` layers, `ℓ_rel = M¹⁶` and `G = ⌈M^{2/5}⌉` (p.68). -/
noncomputable def gF2 (Gr : (M ℓ G : ℕ) → LayeredGraph M) (M : ℕ → ℕ) (lam : ℕ) :
    LayeredGraph (M lam) :=
  Gr (M lam) (M lam ^ 16) (gPar (M lam))

/-- A **sampler state** `st = (D, H, J, Φ, T)` of Construction F.2 (p.69): the full observation `D`,
the honest bit `H`, the signed weights `J_j`, the labels `Φ_j`, and the candidate rows `T_j(ζ)`. -/
abbrev StF (Yc : Type) (M : ℕ → ℕ) (lam h : ℕ) : Type :=
  (Fin (nF M lam) → ∀ j : Fin 1, oneY Yc j) × Bool ×
    (Fin (M lam) → Bool → Bool → (∀ j : Fin 1, oneY Yc j) → Fin (tF M lam + 1)) ×
    (Fin (M lam) → Fin 3) × (Fin (M lam) → Fin h → Fin (tF M lam) → Bool × Bool)

/-- The coins of `SampleSt_rel`: the honest reference state `Θ⁰`, the full observation `D` and the
permutations `π_{j,ζ}`. -/
abbrev BaseF (Yc : Type) (M : ℕ → ℕ) (lam h : ℕ) : Type :=
  (Fin (M lam) → Fin (tF M lam) → Bool × Bool) × (Fin (nF M lam) → ∀ j : Fin 1, oneY Yc j) ×
    (Fin (M lam) → Fin h → Equiv.Perm (Fin (tF M lam)))

open Classical in
/-- `Gen_rel(1^λ)` (Construction F.2, p.68): for each `j ∈ [M]`, a row `θ_j` uniform among the words
containing exactly `t/4` copies of every pair in `{0,1} × {−1, 1}`; the law of `Θ = (θ_j)_j` is
uniform on the tuples of balanced rows. -/
noncomputable def genWF (M : ℕ → ℕ) (lam : ℕ) (Θ : Fin (M lam) → Fin (tF M lam) → Bool × Bool) :
    ℝ :=
  if ∀ j, BalancedF (M lam) (Θ j) then
    1 / ((Finset.univ.filter fun Θ' : Fin (M lam) → Fin (tF M lam) → Bool × Bool =>
      ∀ j, BalancedF (M lam) (Θ' j)).card : ℝ)
  else 0

/-- `Word_rel(Θ)` (p.68): the inputs `a_{x_{j,s}}` in row order. -/
def wordF (a : Bool → X) (M : ℕ → ℕ) (lam : ℕ) (Θ : Fin (M lam) → Fin (tF M lam) → Bool × Bool) :
    Fin (nF M lam) → X :=
  fun p => a (Θ (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1

set_option synthInstance.maxSize 2048 in
open Classical in
/-- The law of the coins of `SampleSt_rel` (p.69: "Sample the honest experiment `(Θ⁰, D)`"):
`Θ⁰ ← Gen_rel(1^λ)`, `D ← C^{n_rel}(Word_rel(Θ⁰))`, and for every `j`, `ζ` an independent uniform
coordinate permutation `π_{j,ζ}` preserving the equal-`D_j` position sets. -/
noncomputable def baseWF (C : DMC X Yc) (a : Bool → X) (M : ℕ → ℕ) (lam h : ℕ)
    (b : BaseF Yc M lam h) : ℝ :=
  genWF M lam b.1 * (∏ p, jointP (oneC C) (wordF a M lam b.1 p) (b.2.1 p)) *
    ∏ j, ∏ ζ, presW (rowOf b.2.1 j) (b.2.2 j ζ)

/-- The sampler state returned by `SampleSt_rel` on its coins (p.69): `H = Q_{Θ⁰}(D)`,
`J_j = J(θ⁰_j, D_j)` (the signed weight `J_{x,e,y} = |{s : x_s = x, ε_s = e, d_s = y}|` of (5.11)
with the binary nominal alphabet), `Φ_j = Φ_{θ⁰_j}(D_j)`, `T_j(ζ) = π_{j,ζ} θ⁰_j` ("each signed pair
moves together"); "Discard `Θ⁰` and return `st = (D, H, J, Φ, T)`". -/
noncomputable def stOfF (C : DMC X Yc) (a : Bool → X) (ystar : Yc)
    (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (M : ℕ → ℕ) (lam h : ℕ) (b : BaseF Yc M lam h) :
    StF Yc M lam h :=
  (b.2.1, testF C a ystar apx M lam b.1 (fun p => b.2.1 p 0),
    fun j => signedWeight (X := Bool) (b.1 j) (rowOf b.2.1 j),
    fun j => labelF C a ystar apx lam (b.1 j) (fun s => rowOf b.2.1 j s 0),
    fun j ζ => permRow (b.2.2 j ζ) (b.1 j))

open Classical in
/-- The **recovery algorithm** `Rec_rel(st, w)` of Construction F.2 (p.69): the empty list if
`H = 1`; otherwise, with `L^raw_j(w_j) = {ζ ∈ H_rel : h_{T_j(ζ)}(w_j) = 1}` if `Φ_j = R` and `∅`
otherwise, and `L_j(w_j) = L^raw_j(w_j)` if `|L^raw_j(w_j)| ≤ ℓ_rel = M¹⁶`, `∅` otherwise, return
`Rec_{G_rel}(⋃_j {j} × L_j(w_j))`. -/
noncomputable def recF2 (C : DMC X Yc) (a : Bool → X) (ystar : Yc)
    (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (M : ℕ → ℕ) (lam : ℕ) (G : LayeredGraph (M lam))
    (st : StF Yc M lam G.h) (w : Fin (nF M lam) → Yc) : List (Fin G.κ → Bool) :=
  if st.2.1 then [] else
  let raw : Fin (M lam) → Finset (Fin G.h) := fun j =>
    if st.2.2.2.1 j = 1 then
      Finset.univ.filter fun ζ => rowF C a ystar apx lam (st.2.2.2.2 j ζ) (rowOf w j) = true
    else ∅
  let L : Fin (M lam) → Finset (Fin G.h) := fun j => if (raw j).card ≤ M lam ^ 16 then raw j else ∅
  G.recov (Finset.univ.filter fun p : Fin (M lam) × Fin G.h => p.2 ∈ L p.1)

/-- The encoding of a signed row: two bits per entry (nominal input, sign). -/
def rowEncF {t : ℕ} (θ : Fin t → Bool × Bool) : List Bool :=
  (List.ofFn fun s => [(θ s).1, (θ s).2]).flatten

/-- The encoding of a sampler state of Construction F.2: the symbols of `D`, the bit `H`, the signed
weights in binary (in a fixed enumeration of the output alphabet), the labels in two bits, and the
candidate rows. -/
noncomputable def stEncF {M : ℕ → ℕ} {lam h : ℕ} (st : StF Yc M lam h) : List Bool :=
  QAdvFew.PoQOracle.tup [wordEnc (∀ j : Fin 1, oneY Yc j) st.1, [st.2.1],
    (List.ofFn fun j : Fin (M lam) => (List.ofFn fun x : Fin 2 => (List.ofFn fun e : Fin 2 =>
      (List.ofFn fun c : Fin (Fintype.card (∀ j : Fin 1, oneY Yc j)) =>
        binW (Nat.size (tF M lam)) (st.2.2.1 j (x = 1) (e = 1)
          ((Fintype.equivFin (∀ j : Fin 1, oneY Yc j)).symm c)).val).flatten).flatten).flatten).flatten,
    (List.ofFn fun j => binW 2 (st.2.2.2.1 j).val).flatten,
    (List.ofFn fun j : Fin (M lam) => (List.ofFn fun ζ : Fin h =>
      rowEncF (st.2.2.2.2 j ζ)).flatten).flatten]

set_option synthInstance.maxSize 2048 in
open Classical in
/-- **Construction F.2 (Verifiable release test)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), pp.67–69), for the channel constants `(a₀, a₁, q* = q_{y*})`, the
public rational approximations `apx`, the row count `M`, and the release expander `G_rel` of the
family `Gr`:
* `Gen_rel(1^λ)`: `M` independent uniform balanced signed rows; `Word_rel(Θ)`: the inputs
  `a_{x_{j,s}}` in row order; `Q_Θ(w) = 1[∑_j h_{θ_j}(w_j) > M/2]`;
* `Valid_rel(Θ) = 1` iff `Θ` consists of `M` balanced signed rows of length `t`;
* `SampleSt_rel(1^λ)`: sample `(Θ⁰, D)`, record `H = Q_{Θ⁰}(D)`, the signed weights, the labels
  (F.3), the candidate rows `T_j(ζ) = π_{j,ζ}θ⁰_j`, and return `st = (D, H, J, Φ, T)` with
  `obs(st) = D`, `H(st) = H`;
* `Recons_rel(st, σ)`: `θ_j = T_j(γ^rel_j(σ))`; `Rec_rel(st, w)`: `recF2`.

**Formalization Note** Secret states range over all `M`-tuples of signed rows of length `t` (so
that `Valid_rel` is meaningful); `Gen_rel` is uniform on the valid ones. The law of `SampleSt_rel`
is the push-forward of the law of its coins. Queries are typed words, so there are no malformed
queries. The bit and support predicates use the true channel; only the count centres of (F.1) use
`apx` (§5 Conventions, p.21; p.68: "the posterior classes are not recomputed from rounded
probabilities"). -/
noncomputable def releaseF2 (C : DMC X Yc) (a : Bool → X) (ystar : Yc)
    (apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ) (M : ℕ → ℕ) (Gr : (M ℓ G : ℕ) → LayeredGraph M) :
    VerReleaseTest X Yc (nF M) where
  Sec lam := Fin (M lam) → Fin (tF M lam) → Bool × Bool
  finSec lam := inferInstance
  genW lam Θ := genWF M lam Θ
  enc lam Θ := (List.ofFn fun j => rowEncF (Θ j)).flatten
  word lam Θ := wordF a M lam Θ
  test lam Θ w := testF C a ystar apx M lam Θ w
  κ lam := (gF2 Gr M lam).κ
  St lam := StF Yc M lam (gF2 Gr M lam).h
  finSt lam := by classical exact inferInstance
  sampW lam st := wprob (baseWF C a M lam (gF2 Gr M lam).h)
    (fun b => stOfF C a ystar apx M lam (gF2 Gr M lam).h b = st)
  encSt lam st := stEncF st
  obs lam st j p := st.1 p j
  H lam st := st.2.1
  recons lam st σ := fun j => st.2.2.2.2 j ((gF2 Gr M lam).γ j σ)
  recov lam st w := recF2 C a ystar apx M lam (gF2 Gr M lam) st w
  valid lam Θ := decide (∀ j, BalancedF (M lam) (Θ j))

end NoisyOWMPC.Supplement


