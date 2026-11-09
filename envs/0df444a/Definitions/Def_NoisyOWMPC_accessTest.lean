-- Prove2me | Definitions.Def_NoisyOWMPC_accessTest
-- name    : NoisyOWMPC_accessTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:54:13.930701+00:00
-- url     : https://prove2.me/theorems/9f7e9159-b241-45eb-b541-a71c45eebb13
-- title:
--   Construction 5.6: the access test with its proof-side algorithms
-- statement:
--   Fix $k>1$, receiver $i$, $E=\mathbf C_{-i}$ with output alphabet $\mathcal Z=\prod_{i'\ne i}\mathcal Y_{i'}$, rows of length $t=M^2$ ($n=M^3$), a threshold $\tau_{\mathrm{acc}}$ and the expander $\mathcal G_{\mathrm{acc}}$ with $\ell_{\mathrm{acc}}=M^2$, $G=\lceil M^{2/5}\rceil$. Construction 5.6 is:
--   1. $\mathrm{Gen}$, $\mathrm{Word}$, $A_\Omega$ as in the protocol half;
--   2. $\mathrm{SampleSt}$: sample $\Omega^0_i\leftarrow\mathcal X^n$ and $Z\leftarrow E^n(\Omega^0_i)$; retain the weights $J_j=J(\Omega^0_{i,j},Z_j)$; for each row $j$ and label $\zeta$ apply an independent uniform permutation $\pi_{j,\zeta}$ preserving the equal-$Z_j$ position sets, $T_j(\zeta)=\pi_{j,\zeta}\Omega^0_{i,j}$; return $\mathrm{st}=(Z,J,T)$ with $\mathrm{obs}(\mathrm{st})=Z$, $H(\mathrm{st})=0$;
--   3. $\mathrm{Recons}(\mathrm{st},\sigma)$: the rows $T_j(\gamma_j(\sigma))$;
--   4. $\mathrm{Rec}(\mathrm{st},y)$: with the recovery predicate (5.10)
--   $$\mathrm{Hit}_{z,J}(x,y)=\mathbf 1\bigl[\|\widehat P_{x,y}-(J/t)K_{z,y}\|_1\ge4\tau_{\mathrm{acc}}\bigr],$$
--   $L^{\mathrm{raw}}_j=\{\zeta:\mathrm{Hit}_{Z_j,J_j}(T_j(\zeta),y_j)=1\}$, truncated to $\emptyset$ above $\ell_{\mathrm{acc}}$; return $\mathrm{Rec}_{\mathcal G_{\mathrm{acc}}}(\bigcup_j\{j\}\times L_j)$.
--
--   **Formalization Note** The expander is the graph of a family as in Corollary A.8; $K_{z,y}(b\mid c)$ uses a given stochastic row $e_0$ on empty position sets ("use any stochastic row for an empty set"); the law of $\mathrm{SampleSt}$ is the push-forward of the law of its coins.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §5.2.1, pp.24–25; Construction 5.6, p.25

import Mathlib
import Definitions.Def_NoisyOWMPC_accessHalf
import Definitions.Def_NoisyOWMPC_ChannelTest
import Definitions.Def_NoisyOWMPC_LayeredGraph
import Definitions.Def_KarpLiptonOM_binW

namespace NoisyOWMPC

open LaconicBarrier KarpLiptonOM

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The output alphabet `Z = ∏_{i′ ≠ i} Y_{i′}` of the channel `E = C_{−i}` (Ishai, Lu, Zafar, STOC
2027 submission (manuscript sha256 3a9569fa…), §5.2.1 Parameters, p.24: "abbreviate `E = C_{−i}`
and `Z = ∏_{i′≠i} Y_{i′}`"), indexed by the observer set `[k] ∖ {i}`. -/
abbrev ZOut (Y : Fin k → Type) (i : Fin k) : Type :=
  ∀ j : {j : Fin k // j ∈ Finset.univ.erase i}, Y j

/-- The transition probability `E(z | x) = ∏_{j ≠ i} C_j(z_j | x)` of `E = C_{−i}` (p.24). -/
def otherP (C : ∀ j, DMC X (Y j)) (i : Fin k) (x : X) (z : ZOut Y i) : ℝ :=
  ∏ j : {j : Fin k // j ∈ Finset.univ.erase i}, (C j).P x (z j)

/-- The `j`th consecutive length-`t` row of a word of length `M · t` (p.24: "For a length-`n`
word, a subscript `j ∈ [M]` denotes its `j`th consecutive length-`t` row"). -/
def rowOf {α : Type} {M t : ℕ} (w : Fin (M * t) → α) (j : Fin M) : Fin t → α :=
  fun s => w (finProdFinEquiv (j, s))

/-- A word of length `M³` read as a word of length `M · M²` (rows of length `t = M²`, p.24). -/
def asRows {α : Type} {M : ℕ} (w : Fin (M ^ 3) → α) : Fin (M * M ^ 2) → α :=
  fun p => w (Fin.cast (by ring) p)

/-- A coordinate permutation `π` **preserves the equal-`z` position sets** of `z ∈ Zᵗ` (p.25:
"uniform coordinate permutation `π_{j,ζ}` preserving the equal-`Z_j` position sets"). -/
def PresSets {α : Type} {t : ℕ} (z : Fin t → α) (π : Equiv.Perm (Fin t)) : Prop :=
  ∀ s, z (π s) = z s

/-- The permuted row `πx`, `(πx)_s = x_{π⁻¹(s)}` (p.25: "`T_j(ζ) = π_{j,ζ} Ω⁰_{i,j}`"). -/
def permRow {α : Type} {t : ℕ} (π : Equiv.Perm (Fin t)) (x : Fin t → α) : Fin t → α :=
  fun s => x (π.symm s)

open Classical in
/-- The uniform weight on the permutations of `[t]` preserving the equal-`z` position sets. -/
noncomputable def presW {α : Type} {t : ℕ} (z : Fin t → α) (π : Equiv.Perm (Fin t)) : ℝ :=
  if PresSets z π then 1 / ((Finset.univ.filter fun ρ => PresSets z ρ).card : ℝ) else 0

open Classical in
/-- The **weight** `J(x, z) = (J_{a,c}(x, z))_{a,c}`, `J_{a,c}(x, z) = |{s : x_s = a, z_s = c}|`, of
`(x, z) ∈ Xᵗ × Zᵗ` (p.24). -/
noncomputable def accWeight {Z : Type} {t : ℕ} (x : Fin t → X) (z : Fin t → Z) :
    X → Z → Fin (t + 1) :=
  fun a c => ⟨(Finset.univ.filter fun s => x s = a ∧ z s = c).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

/-- The expander parameter `G = ⌈M^{2/5}⌉` (pp.25–26). -/
noncomputable def gPar (M : ℕ) : ℕ := ⌈(M : ℝ) ^ ((2 : ℝ) / 5)⌉₊

/-- The access expander `G_acc`: the layered `(M ℓ_acc, G, L_out)`-list-recoverable graph of the
family `Gr` with `M` layers, `ℓ_acc = M²` and `G = ⌈M^{2/5}⌉` (p.25). -/
noncomputable def gAcc (Gr : (M ℓ G : ℕ) → LayeredGraph M) (M : ℕ → ℕ) (lam : ℕ) : LayeredGraph (M lam) :=
  Gr (M lam) (M lam ^ 2) (gPar (M lam))

/-- A **sampler state of the access test** `st = (Z, J, T)` (Construction 5.6, `SampleSt_acc,i`,
p.25): the other receivers' observation `Z ∈ Zⁿ`, the row weights `J_j`, and the candidate rows
`T_j(ζ) ∈ Xᵗ` for `j ∈ [M]`, `ζ ∈ H_acc`. -/
abbrev AccSt (X : Type) (Y : Fin k → Type) (i : Fin k) (M h : ℕ) : Type :=
  (Fin (M ^ 3) → ZOut Y i) × (Fin M → X → ZOut Y i → Fin (M ^ 2 + 1)) × (Fin M → Fin h → Fin (M ^ 2) → X)

/-- The coins of `SampleSt_acc,i`: the word `Ω⁰_i`, the observation `Z`, and the permutations
`π_{j,ζ}`. -/
abbrev AccBase (X : Type) (Y : Fin k → Type) (i : Fin k) (M h : ℕ) : Type :=
  (Fin (M ^ 3) → X) × (Fin (M ^ 3) → ZOut Y i) × (Fin M → Fin h → Equiv.Perm (Fin (M ^ 2)))

open Classical in
/-- The law of the coins of `SampleSt_acc,i` (p.25): `Ω⁰_i` uniform on `Xⁿ`, `Z ← Eⁿ(Ω⁰_i)`, and
independent uniform permutations `π_{j,ζ}` preserving the equal-`Z_j` position sets. -/
noncomputable def accBaseW (C : ∀ j, DMC X (Y j)) (i : Fin k) (M h : ℕ)
    (b : AccBase X Y i M h) : ℝ :=
  unifW (Fin (M ^ 3) → X) b.1 * (∏ p, otherP C i (b.1 p) (b.2.1 p)) *
    ∏ j, ∏ ζ, presW (rowOf (asRows b.2.1) j) (b.2.2 j ζ)

/-- The sampler state returned by `SampleSt_acc,i` on its coins (p.25): "For each row `j`, retain
the weight `J_j = J(Ω⁰_{i,j}, Z_j)` … set `T_j(ζ) = π_{j,ζ} Ω⁰_{i,j}`. Discard `Ω⁰_i` and return
`st = (Z, J, T)`". -/
noncomputable def accStOf {i : Fin k} {M h : ℕ} (b : AccBase X Y i M h) : AccSt X Y i M h :=
  (b.2.1, fun j => accWeight (rowOf (asRows b.1) j) (rowOf (asRows b.2.1) j),
    fun j ζ => permRow (b.2.2 j ζ) (rowOf (asRows b.1) j))

open Classical in
/-- The stochastic map `K_{z,y}(b | c)` (p.25): "the fraction of positions with query symbol `b`
among those with `z_s = c`; use any stochastic row for an empty set" — the row `e₀` is used for an
empty set. -/
noncomputable def kzy {i : Fin k} {Z : Type} {t : ℕ} (e0 : Y i → ℚ) (z : Fin t → Z) (y : Fin t → Y i)
    (b : Y i) (c : Z) : ℚ :=
  if 0 < (Finset.univ.filter fun s => z s = c).card then
    ((Finset.univ.filter fun s => z s = c ∧ y s = b).card : ℚ) /
      ((Finset.univ.filter fun s => z s = c).card : ℚ)
  else e0 b

open Classical in
/-- The **recovery predicate** (5.10) (p.25): `Hit_{z,J}(x, y) = 1[‖P̂_{x,y} − μ_{z,J}(y)‖₁ ≥ 4τ_acc]`
with `μ_{z,J}(y) = (J/t) K_{z,y}`, i.e. `μ(a, b) = ∑_c (J_{a,c}/t) K_{z,y}(b | c)`, and the
empirical pair distribution `P̂_{x,y}(a, b) = N_{a,b}(x, y)/t`. -/
noncomputable def accHit {i : Fin k} {Z : Type} [Fintype Z] (τ : ℚ) (e0 : Y i → ℚ) {t : ℕ} (z : Fin t → Z)
    (J : X → Z → Fin (t + 1)) (x : Fin t → X) (y : Fin t → Y i) : Prop :=
  4 * τ ≤ ∑ a, ∑ b, |((Finset.univ.filter fun s => x s = a ∧ y s = b).card : ℚ) / t -
    ∑ c, ((J a c : ℕ) : ℚ) / t * kzy e0 z y b c|

open Classical in
/-- The **recovery algorithm of the access test** (Construction 5.6, `Rec_acc,i`, p.25): with
`L^raw_j(y_j) = {ζ ∈ H_acc : Hit_{Z_j,J_j}(T_j(ζ), y_j) = 1}` and `L_j(y_j) = L^raw_j(y_j)` if
`|L^raw_j(y_j)| ≤ ℓ_acc = M²`, `∅` otherwise, return `Rec_{G_acc}(⋃_j {j} × L_j(y_j))`. -/
noncomputable def accRec {i : Fin k} {M : ℕ} (G : LayeredGraph M) (τ : ℚ) (e0 : Y i → ℚ)
    (st : AccSt X Y i M G.h) (y : Fin (M ^ 3) → Y i) : List (Fin G.κ → Bool) :=
  let raw : Fin M → Finset (Fin G.h) := fun j => Finset.univ.filter fun ζ =>
    accHit τ e0 (rowOf (asRows st.1) j) (st.2.1 j) (st.2.2 j ζ) (rowOf (asRows y) j)
  let L : Fin M → Finset (Fin G.h) := fun j => if (raw j).card ≤ M ^ 2 then raw j else ∅
  G.recov (Finset.univ.filter fun p : Fin M × Fin G.h => p.2 ∈ L p.1)

/-- The **reconstruction** `Recons_acc,i(st, σ)` (p.25): "Concatenate the rows `T_j(γ^acc_j(σ))`". -/
def accRecons {i : Fin k} {M : ℕ} (G : LayeredGraph M) (st : AccSt X Y i M G.h)
    (σ : Fin G.κ → Bool) : Fin (M ^ 3) → X :=
  fun p => let q := finProdFinEquiv.symm (Fin.cast (by ring : M ^ 3 = M * M ^ 2) p)
    st.2.2 q.1 (G.γ q.1 σ) q.2

/-- The encoding of an access sampler state: the symbols of `Z`, the entries of the weights `J_j` in
binary (inputs and outputs in a fixed enumeration), and the symbols of the candidate rows. -/
noncomputable def accStEnc {i : Fin k} {M h : ℕ} (st : AccSt X Y i M h) : List Bool :=
  QAdvFew.PoQOracle.tup [wordEnc (ZOut Y i) st.1,
    (List.ofFn fun j : Fin M => (List.ofFn fun a : Fin (Fintype.card X) =>
      (List.ofFn fun c : Fin (Fintype.card (ZOut Y i)) =>
        binW (Nat.size (M ^ 2)) (st.2.1 j ((Fintype.equivFin X).symm a)
          ((Fintype.equivFin (ZOut Y i)).symm c)).val).flatten).flatten).flatten,
    (List.ofFn fun j : Fin M => (List.ofFn fun ζ : Fin h => wordEnc X (st.2.2 j ζ)).flatten).flatten]

open Classical in
/-- **Construction 5.6 (Access test)** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), p.25), with the global predicate (5.9), the recovery predicate (5.10) with threshold
`τ_acc` and empty-set row `e₀`, and the access expander `G_acc` of the family `Gr`:
* `Gen_acc,i`, `Word_acc,i`, `A_{Ω_i}`: the protocol half `accessHalfN` at `n = M³`;
* `SampleSt_acc,i(1^λ)`: sample `Ω⁰_i ← Xⁿ` and `Z ← Eⁿ(Ω⁰_i)`, retain `J_j = J(Ω⁰_{i,j}, Z_j)`,
  set `T_j(ζ) = π_{j,ζ} Ω⁰_{i,j}` for independent uniform permutations preserving the equal-`Z_j`
  position sets, and return `st = (Z, J, T)` with `obs(st) = Z` and `H(st) = 0`;
* `Recons_acc,i(st, σ)`: the rows `T_j(γ^acc_j(σ))`; `Rec_acc,i(st, y)`: `accRec`.

**Formalization Note** The law of `SampleSt` is the push-forward of the law of its coins (exact
reference distribution, p.24); the channel probabilities in (5.9) are the approximations `apx`
(§5 Conventions, p.21). Queries are typed words, so there are no malformed queries. -/
noncomputable def accessTest (C : ∀ j, DMC X (Y j)) (apx : ℕ → ∀ i, X → Y i → ℚ) (M : ℕ → ℕ)
    (i : Fin k) (Gr : (M ℓ G : ℕ) → LayeredGraph M) (τ : ℚ) (e0 : Y i → ℚ) :
    ChannelTest k X Y i (fun lam => M lam ^ 3) (Finset.univ.erase i) where
  toTestHalf := accessHalfN apx M i (fun lam => M lam ^ 3)
  κ lam := (gAcc Gr M lam).κ
  St lam := AccSt X Y i (M lam) (gAcc Gr M lam).h
  finSt lam := inferInstance
  sampW lam st := wprob (accBaseW C i (M lam) (gAcc Gr M lam).h) (fun b => accStOf b = st)
  encSt lam st := accStEnc st
  obs lam st j p := st.1 p j
  H _ _ := false
  recons lam st σ := accRecons (gAcc Gr M lam) st σ
  recov lam st y := accRec (gAcc Gr M lam) τ e0 st y

end NoisyOWMPC


