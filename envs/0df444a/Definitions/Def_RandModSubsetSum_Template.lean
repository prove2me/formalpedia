-- Prove2me | Definitions.Def_RandModSubsetSum_Template
-- name    : RandModSubsetSum_Template
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:24.770317+00:00
-- url     : https://prove2.me/theorems/f044de6b-a2d9-439b-a881-f2a4b47a0e35
-- title:
--   Representations of a root, the auxiliary residue model, difference spans and $\mu_W$
-- statement:
--   **Template** (§3.1). Depth $d=7$, alphabets $A_0=\{0,1\}$ and $A_i=\{-q_i,\dots,q_i\}$ with $(q_1,\dots,q_7)=(3,3,2,2,1,1,1)$. A **representation** of a binary root $x$ assigns a length-$n$ word $v_{i,v}\in A_i^n$ to each of the $2^i$ slots at depth $i$, with $v_{0,1}=x$ and $v_{j,v}=v_{j+1,2v-1}+v_{j+1,2v}$ coordinatewise.
--
--   **Auxiliary residue model** (§3.1, §4.1). For moduli $p_1,\dots,p_7$, the coefficient vectors $a_i\in\mathbb F_{p_i}^n$ are independent and uniform, and given them the labels $(\ell_{i,v})_{v\le 2^i}$ are uniform among the tuples with $\sum_v\ell_{i,v}=a_i\cdot x$, independently across $i$. A representation $D$ **matches** all residue labels if $a_i\cdot v_{i,v}=\ell_{i,v}$ in $\mathbb F_{p_i}$ for every $i,v$. For a finite family $\mathcal D$, $Z=\sum_{D\in\mathcal D}I_D$ counts its matching members; the module defines $\mathbb E$, $\Pr$, $\mathrm{Var}(Z)/\mathbb E(Z)^2$ and $\Pr(Z=0)$ in this model.
--
--   **Difference spans** (§4.1). For $D,D'$ put $b_k=(v_{7,v}[k]-v'_{7,v}[k])_{v=1}^{128}$ and $W(D,D')=\mathrm{span}_{\mathbb Q}\{b_1,\dots,b_n\}\le H=\{z\in\mathbb Q^{128}:\sum_v z_v=0\}$. The map $\pi_i$ sums the leaves below each depth-$i$ slot; $s_i=2^i-1-\dim\pi_iW$, $\chi_i=s_i-s_{i-1}$, $s_0=0$. With $C_W(D)=\{D'\in\mathcal D:W(D,D')\subseteq W\}$,
--   $$\mu_W=\max_{D\in\mathcal D}\frac{|C_W(D)|}{|\mathcal D|},\qquad \mathcal W=\{W(D,D'):D,D'\in\mathcal D\}.$$
--
--   These are the objects of Lemmas 4.1–4.3.
--
--   **Formalization Note** Slots and depths are 0-indexed: the children of slot $v$ at depth $j$ are $2v$ and $2v+1$. Index $i\in\{0,\dots,6\}$ of the moduli and labels stands for depth $i+1$. The model is the uniform distribution on the finite set of samples whose labels have the prescribed sums; this is the same law, because every coefficient vector has the same number $\prod_ip_i^{2^i-1}$ of label tuples. Residues are stored by their representatives in $\{0,\dots,p-1\}$. Rates are stored as $K_{i+1}$ at index $i$, with `Knext` giving $K_{i+2}$ and the convention $K_8=0$.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), §3.1, pp. 11–13; §4.1, pp. 19–20

import Mathlib
import Definitions.Def_RandModSubsetSum_Types

open scoped BigOperators

namespace RandModSubsetSum

/-- The alphabet radii `(q₁, …, q₇) = (3, 3, 2, 2, 1, 1, 1)` of the representation template
(§3.1, p. 11). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027
submission manuscript (sha256 c37a38c7…f89), §3.1, p. 11. Values outside `1..7` are unused. -/
def radius : ℕ → ℕ
  | 1 => 3
  | 2 => 3
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | _ => 0

/-- The alphabets `A₀ = {0, 1}` and `A_i = {−q_i, …, q_i}` for `1 ≤ i ≤ 7` (§3.1, p. 11). -/
noncomputable def alph : ℕ → Finset ℤ
  | 0 => {0, 1}
  | i + 1 => Finset.Icc (-(radius (i + 1) : ℤ)) (radius (i + 1))

/-- A tree of words for the depth-7 template: the word at slot `v` of depth `i` (`2^i` slots,
0-indexed) is a length-`n` integer word. The children of slot `v` at depth `j` are the slots `2v`
and `2v + 1` at depth `j + 1` (the paper's `2v − 1, 2v` in 1-indexed form). -/
abbrev Rep (n : ℕ) := (i : Fin 8) → Fin (2 ^ i.val) → Fin n → ℤ

/-- `D` is a **representation** of the binary root `x` (§3.1, p. 11): `v_{0,1} = x`,
`v_{j,v} = v_{j+1,2v−1} + v_{j+1,2v}` coordinatewise for `0 ≤ j < 7`, and the word at depth `i`
belongs to `A_iⁿ`. -/
def IsRepOf {n : ℕ} (x : Fin n → Fin 2) (D : Rep n) : Prop :=
  (∀ k, D 0 ⟨0, Nat.two_pow_pos _⟩ k = ((x k).val : ℤ)) ∧
  (∀ (j : ℕ) (hj : j < 7) (v : Fin (2 ^ j)) (k : Fin n),
      D ⟨j, by omega⟩ v k =
        D ⟨j + 1, by omega⟩ ⟨2 * v.val, by have := v.2; rw [pow_succ]; omega⟩ k +
        D ⟨j + 1, by omega⟩ ⟨2 * v.val + 1, by have := v.2; rw [pow_succ]; omega⟩ k) ∧
  (∀ (i : Fin 8) (v : Fin (2 ^ i.val)) (k : Fin n), D i v k ∈ alph i.val)

/-- Every tree whose entries lie in `{−3, …, 3}` (all alphabets are contained in it): the image of
the finite set of `{0, …, 6}`-valued trees under `e ↦ e − 3`. Used to make families of
representations finite sets. -/
noncomputable def boundedReps (n : ℕ) : Finset (Rep n) :=
  haveI : DecidableEq (Rep n) := Classical.decEq _
  (Finset.univ : Finset ((i : Fin 8) → Fin (2 ^ i.val) → Fin n → Fin 7)).image
    (fun E i v k => ((E i v k).val : ℤ) - 3)

/-- A sample of the **auxiliary residue model** (§3.1, p. 13; §4.1, p. 19) for moduli
`p : Fin 7 → ℕ` (`p i` is the paper's `p_{i+1}`): for each depth `i + 1 = 1, …, 7`, a coefficient
vector `a_{i+1} ∈ F_{p_{i+1}}ⁿ` and the labels `(ℓ_{i+1,v})_{v}` of the `2^{i+1}` slots at that
depth. Residues are stored by their representatives in `{0, …, p − 1}`. -/
abbrev AuxSample (n : ℕ) (p : Fin 7 → ℕ) :=
  (i : Fin 7) → (Fin n → Fin (p i)) × (Fin (2 ^ (i.val + 1)) → Fin (p i))

open Classical in
/-- The support of the auxiliary residue model for the root `x`: the samples whose labels at every
depth sum to `t_i = a_i · x` in `F_{p_i}` (p. 12: "sample the labels of the `2^i` slots at depth `i`
uniformly subject to `Σ_v ℓ_{i,v} = t_i`"). The model is the **uniform distribution** on this finite
set: the coefficient vectors are independent and uniform, and, given them, the labels are uniform
among the tuples with the prescribed sums, independently across depths (every coefficient vector
has the same number `Π_i p_i^{2^i − 1}` of label tuples). -/
noncomputable def auxSpace {n : ℕ} (p : Fin 7 → ℕ) (x : Fin n → Fin 2) : Finset (AuxSample n p) :=
  Finset.univ.filter (fun ω => ∀ i : Fin 7,
    ∑ v, (((ω i).2 v).val : ZMod (p i)) =
      ∑ k, (((ω i).1 k).val : ZMod (p i)) * (((x k).val : ℕ) : ZMod (p i)))

/-- `D` **matches all residue labels** of the sample `ω` (§3.1, pp. 12–13): for every depth
`i = 1, …, 7` and slot `v`, `a_i · v_{i,v} = ℓ_{i,v}` in `F_{p_i}`. (The inherited conditions (3)
then hold automatically.) -/
def Matches {n : ℕ} {p : Fin 7 → ℕ} (D : Rep n) (ω : AuxSample n p) : Prop :=
  ∀ (i : Fin 7) (v : Fin (2 ^ (i.val + 1))),
    ∑ k, (((ω i).1 k).val : ZMod (p i)) * ((D ⟨i.val + 1, by omega⟩ v k : ℤ) : ZMod (p i)) =
      (((ω i).2 v).val : ZMod (p i))

/-- Probability of an event in the auxiliary residue model (uniform on `auxSpace`). -/
noncomputable def auxProb {n : ℕ} (p : Fin 7 → ℕ) (x : Fin n → Fin 2)
    (E : AuxSample n p → Prop) : ℝ :=
  haveI : DecidablePred E := Classical.decPred _
  ((auxSpace p x).filter E).card / (auxSpace p x).card

/-- Expectation of a real random variable in the auxiliary residue model. -/
noncomputable def auxMean {n : ℕ} (p : Fin 7 → ℕ) (x : Fin n → Fin 2)
    (f : AuxSample n p → ℝ) : ℝ :=
  (∑ ω ∈ auxSpace p x, f ω) / (auxSpace p x).card

open Classical in
/-- `Z = Σ_{D ∈ 𝒟} I_D`, the number of members of a family `𝒟` matching all residue labels
(§4.1, p. 19). -/
noncomputable def Zcount {n : ℕ} {p : Fin 7 → ℕ} (𝒟 : Finset (Rep n)) (ω : AuxSample n p) : ℕ :=
  (𝒟.filter (fun D => Matches D ω)).card

/-- The normalized variance `Var(Z) / E(Z)²` in the auxiliary residue model. -/
noncomputable def varRatio {n : ℕ} (p : Fin 7 → ℕ) (x : Fin n → Fin 2) (𝒟 : Finset (Rep n)) : ℝ :=
  (auxMean p x (fun ω => (Zcount 𝒟 ω : ℝ) ^ 2) - (auxMean p x (fun ω => (Zcount 𝒟 ω : ℝ))) ^ 2) /
    (auxMean p x (fun ω => (Zcount 𝒟 ω : ℝ))) ^ 2

/-- `Pr(Z = 0)` in the auxiliary residue model. -/
noncomputable def probNoMatch {n : ℕ} (p : Fin 7 → ℕ) (x : Fin n → Fin 2) (𝒟 : Finset (Rep n)) : ℝ :=
  auxProb p x (fun ω => Zcount 𝒟 ω = 0)

/-- The **difference span** (§4.1, p. 20): with `b_k = (v_{7,v}[k] − v′_{7,v}[k])_{v=1}^{128}`,
`W(D, D′) = span_ℚ {b_1, …, b_n} ≤ ℚ^128`. -/
noncomputable def diffSpan {n : ℕ} (D D' : Rep n) : Submodule ℚ (Fin (2 ^ 7) → ℚ) :=
  Submodule.span ℚ (Set.range (fun k : Fin n => fun v : Fin (2 ^ 7) =>
    ((D (Fin.last 7) v k - D' (Fin.last 7) v k : ℤ) : ℚ)))

/-- `H = {z ∈ ℚ^128 : Σ_v z_v = 0}` (§4.1, p. 20). -/
noncomputable def sumZero : Submodule ℚ (Fin (2 ^ 7) → ℚ) :=
  LinearMap.ker (Fintype.linearCombination ℚ (fun _ : Fin (2 ^ 7) => (1 : ℚ)))

open Classical in
/-- `π_i` (§4.1, p. 20): `(π_i z)_v = Σ_{k = (v−1)2^{7−i}+1}^{v 2^{7−i}} z_k`, summing the leaves
below each depth-`i` slot (0-indexed: the leaves `k` with `⌊k / 2^{7−i}⌋ = v`). -/
noncomputable def proj (i : ℕ) : (Fin (2 ^ 7) → ℚ) →ₗ[ℚ] (Fin (2 ^ i) → ℚ) where
  toFun z v := ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ 7) => k.val / 2 ^ (7 - i) = v.val), z k
  map_add' z z' := by funext v; simp [Finset.sum_add_distrib]
  map_smul' c z := by funext v; simp [Finset.mul_sum]

/-- `s_i(W) = 2^i − 1 − dim π_i W` (§4.1, p. 20), as an integer, for `0 ≤ i ≤ 7`. -/
noncomputable def sDef (W : Submodule ℚ (Fin (2 ^ 7) → ℚ)) (i : ℕ) : ℤ :=
  (2 ^ i : ℤ) - 1 - (Module.finrank ℚ (W.map (proj i)) : ℤ)

/-- `χ_i = s_i − s_{i−1}` with `s_0 = 0` (§4.1, p. 20), for `1 ≤ i ≤ 7`. -/
noncomputable def chi (W : Submodule ℚ (Fin (2 ^ 7) → ℚ)) (i : ℕ) : ℤ :=
  sDef W i - sDef W (i - 1)

open Classical in
/-- `C_W(D) = {D′ ∈ 𝒟 : W(D, D′) ⊆ W}` (§4.1, p. 20). -/
noncomputable def cosetFamily {n : ℕ} (𝒟 : Finset (Rep n)) (W : Submodule ℚ (Fin (2 ^ 7) → ℚ))
    (D : Rep n) : Finset (Rep n) :=
  𝒟.filter (fun D' => diffSpan D D' ≤ W)

/-- `μ_W = max_{D ∈ 𝒟} |C_W(D)| / |𝒟|` (§4.1, p. 20). -/
noncomputable def muW {n : ℕ} (𝒟 : Finset (Rep n)) (W : Submodule ℚ (Fin (2 ^ 7) → ℚ)) : ℝ :=
  ((𝒟.sup (fun D => (cosetFamily 𝒟 W D).card) : ℕ) : ℝ) / (𝒟.card : ℝ)

open Classical in
/-- The family of actual difference spans `𝒲 = {W(D, D′) : D, D′ ∈ 𝒟}` (§4.1, p. 20). -/
noncomputable def spans {n : ℕ} (𝒟 : Finset (Rep n)) : Finset (Submodule ℚ (Fin (2 ^ 7) → ℚ)) :=
  (𝒟 ×ˢ 𝒟).image (fun DD => diffSpan DD.1 DD.2)

/-- The next cumulative rate `K_{i+1}` for rates stored as `K : Fin 7 → ℝ` (`K i` is the paper's
`K_{i+1}`), with the convention `K_8 = 0` (§3.1, p. 12). -/
noncomputable def Knext (K : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  if h : i.val + 1 < 7 then K ⟨i.val + 1, h⟩ else 0

end RandModSubsetSum


