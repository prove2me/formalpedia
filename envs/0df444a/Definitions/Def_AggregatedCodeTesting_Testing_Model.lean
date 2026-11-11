-- Prove2me | Definitions.Def_AggregatedCodeTesting_Testing_Model
-- name    : AggregatedCodeTesting_Testing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:30.215922+00:00
-- url     : https://prove2.me/theorems/8d415d1f-b7df-490f-b5e5-2583bb6d456b
-- title:
--   §§2–4 — aggregated coset samples of a binary linear code: blocks, profiles, laws, Krawtchouk moments, parity, balance, density
-- statement:
--   Fix a binary linear code $C\le\mathbb F_2^m$ (coordinates $1,\dots,m$) and a width $w$. An **offset sequence** is $\ell=(\ell_1,\dots,\ell_w)\in(\mathbb F_2^m)^w$.
--
--   1. **Observation law.** Draw $U_1,\dots,U_w$ independently and uniformly from $C$, put $Y_j=\ell_j+U_j$ (addition in $\mathbb F_2^m$) and observe the labelled vector $H\in\{0,\dots,w\}^m$, $H_e=\sum_{j=1}^w Y_{j,e}$, where the bits are read as the integers $0,1$ and added as integers. $P_\ell(h)$ is the probability that $H=h$; every observation uses fresh masks.
--   2. **Blocks.** For $D\subseteq[m]$ let $\pi_D$ keep the coordinates in $D$ and zero the others. $D$ is **compatible** if $\pi_D(C)\subseteq C$. The block of a coordinate $e$ is the intersection of all compatible sets containing $e$; these atoms form the finest compatible partition $\mathcal B_C$, and $C_D=\pi_D(C)$. $C$ is **indecomposable** if its only compatible sets are $\emptyset$ and $[m]$, and has **no identically zero coordinate** if every coordinate equals $1$ in some codeword. A block is **informative** if $C_D\ne\mathbb F_2^D$ (it has more than one coset); $|Q_D|=2^{|D|}/|C_D|$ is its number of cosets.
--   3. **Profile.** For a block $D$ and a coset $\sigma=x|_D+C_D$ of $Q_D=\mathbb F_2^D/C_D$, $n_{D,\sigma}(\ell)=|\{j:\ell_j|_D+C_D=\sigma\}|$. The **profile** $T_C(\ell)=(n_{D,\sigma}(\ell))_{D,\sigma}$ is the whole family of block-coset counts.
--   4. **Characters.** $C^\perp$ is the dual code for the binary dot product; the block dual $C_D^\perp$ consists of the dual words supported in $D$. A word is identified with its support and $|A|$ is its Hamming weight. $n_A(\ell)=|\{j:A\cdot\ell_j=1\}|$ and $\hat n_A(\ell)=w-2n_A(\ell)\in\mathbb Z$.
--   5. **Moments.** With the binary Krawtchouk polynomials $\sum_j K_j(h)z^j=(1-z)^h(1+z)^{w-h}$, for a multi-index $r$ put $|r|=\sum_e r_e$, $\binom{w}{r}=\prod_e\binom{w}{r_e}$, $\psi_r(h)=\prod_e K_{r_e}(h_e)$ and $c_\ell(r)=\mathbb E_\ell\,\psi_r(H)$; $K_j=0$ for $j>w$. $B$ is the product of $m$ independent $\mathrm{Bin}(w,1/2)$ laws. For two offset sequences of the same width, $s(\ell,\ell')=\min\{|r|:c_\ell(r)\ne c_{\ell'}(r)\}$.
--   6. **Parity.** Profiles are **parity-equivalent** if $n_A(\ell)\equiv n_A(\ell')\pmod 2$ for every $A\in C^\perp$. The **parity class** of $\ell$ is the set of $h$ with $\sum_{e\in A}h_e\equiv n_A(\ell)\pmod 2$ for all $A\in C^\perp$, and $B_\ell$ is $B$ conditioned on it.
--   7. **Balance and density.** $\ell$ is **$M$-balanced** if $|n_{D,\sigma}(\ell)-w/|Q_D||\le M$ for every block coset, and **$\alpha$-dense** if $n_{D,\sigma}(\ell)\ge\alpha w$ for every block coset.
--   8. **Spin cumulant.** For a dual word $A$, $\kappa_C(A)$ is the joint cumulant of the spins $((-1)^{U_e})_{e\in A}$, $U$ uniform on $C$, defined by the moment–cumulant formula $\sum_\pi(-1)^{|\pi|-1}(|\pi|-1)!\prod_{S\in\pi}\mathbb E\prod_{e\in S}(-1)^{U_e}$ over the set partitions $\pi$ of $A$.
--
--   These objects are the model of Sections 2–4: the profile is exactly what the observation law identifies, and the moments, parities, balance and density conditions are the quantities in which the testing theorems are stated.
--
--   **Formalization Note.** A block coset $\sigma$ is indexed by any representative $x\in\mathbb F_2^m$ ($\ell_j$ lies in it iff $\pi_D(\ell_j-x)\in C$); the profile records the count at every representative, which carries the same information. $P_\ell$ is a mass function on $\{0,\dots,w\}^m$ (`Fin m → Fin (w+1)`), computed as the fraction of mask tuples in $C^w$ producing $h$. $K_j(h)$ is the published `MatousekLP.Codes.K w j h`. $\kappa_C(A)$ uses the published `AMPLowDeg.RankOne.cum` under the uniform law on $C$; for a block $D\supseteq A$ the marginal of the uniform law on $C$ on $D$ is uniform on $C_D$, so this is the block cumulant. $s(\ell,\ell')$ takes values in $\mathbb N\cup\{\infty\}$.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), eq. (1)–(2) printed p. 3 (PDF p. 4); §3.1, χ_A, n_A, Krawtchouk moments, s(ℓ,ℓ′), Theorem 3 (cumulant), printed p. 4 (PDF p. 5); balance and parity, printed p. 7 (PDF p. 8); α-density, printed p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_MatousekLP_Codes_DelsarteLP
import Definitions.Def_AMPLowDeg_RankOne_Cumulant

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-! # The aggregated binary linear-code model

Wang–Wang–Pang–Xiao–Zhang–Fu–Zheng–Zou, STOC 2027 submission #1555 (October 2026),
§2 (printed p. 3, PDF p. 4), §3.1 (printed p. 4, PDF p. 5), §4.1 (printed p. 7, PDF p. 8),
§4.2 (printed p. 8, PDF p. 9).

A code is a submodule `C ≤ F₂^m` (`F₂ = ZMod 2`, coordinates `Fin m`). Cosets of a block code
`C_D` are indexed by representatives `x ∈ F₂^m`; every count below is computed from `C`. -/

/-- Binary words of length `m`. -/
abbrev Word (m : ℕ) := Fin m → ZMod 2

variable {m : ℕ}

/-- The dual code `C^⊥ = {A : A · c = 0 for all c ∈ C}` (binary dot product). -/
noncomputable def dualCode (C : Submodule (ZMod 2) (Word m)) : Finset (Word m) :=
  univ.filter fun A => ∀ c ∈ C, dotProduct A c = 0

/-- The support of a binary word (a dual word is identified with its support). -/
noncomputable def supp (x : Word m) : Finset (Fin m) := univ.filter fun e => x e ≠ 0

/-- Hamming weight `|A|`. -/
noncomputable def weight (x : Word m) : ℕ := (supp x).card

/-- `π_D`: keep the coordinates in `D`, zero the others. -/
def proj (D : Finset (Fin m)) (x : Word m) : Word m := fun e => if e ∈ D then x e else 0

/-- A coordinate set `D` is compatible when `π_D(C) ⊆ C`. -/
def IsCompatible (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : Prop :=
  ∀ c ∈ C, proj D c ∈ C

/-- The atom of the Boolean algebra of compatible sets containing `e`: the intersection of all
compatible sets containing `e`. -/
noncomputable def blockOf (C : Submodule (ZMod 2) (Word m)) (e : Fin m) : Finset (Fin m) :=
  univ.filter fun f => ∀ D : Finset (Fin m), IsCompatible C D → e ∈ D → f ∈ D

/-- The finest compatible coordinate partition `B_C` (the blocks), computed from `C`. -/
noncomputable def blocks (C : Submodule (ZMod 2) (Word m)) : Finset (Finset (Fin m)) :=
  univ.image (blockOf C)

/-- `C` is indecomposable: its only compatible sets are `∅` and all coordinates. -/
def IsIndecomposable (C : Submodule (ZMod 2) (Word m)) : Prop :=
  ∀ D : Finset (Fin m), IsCompatible C D → D = ∅ ∨ D = univ

/-- `C` has no identically zero coordinate: every coordinate is `1` in some codeword. -/
def HasNoZeroCoord (C : Submodule (ZMod 2) (Word m)) : Prop :=
  ∀ e : Fin m, ∃ c ∈ C, c e = 1

/-- The block code `C_D = π_D(C)`, i.e. the codewords supported in `D` (for compatible `D`). -/
noncomputable def blockCode (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) :
    Finset (Word m) :=
  univ.filter fun c => c ∈ C ∧ supp c ⊆ D

/-- `|Q_D| = |F₂^D / C_D| = 2^{|D|} / |C_D|`, the number of cosets of the block. -/
noncomputable def numCosets (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : ℝ :=
  (2 : ℝ) ^ D.card / ((blockCode C D).card : ℝ)

/-- A block is informative when it has more than one coset (`C_D ≠ F₂^D`). -/
def IsInformative (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : Prop :=
  ∃ x : Word m, proj D x ∉ C

/-- The informative blocks. -/
noncomputable def informativeBlocks (C : Submodule (ZMod 2) (Word m)) : Finset (Finset (Fin m)) :=
  (blocks C).filter (IsInformative C)

/-- The dual `C_D^⊥` of the block code, as the dual words supported in `D`. -/
noncomputable def blockDual (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) :
    Finset (Word m) :=
  (dualCode C).filter fun A => supp A ⊆ D

/-- `n_{D,σ}(ℓ)` for the block coset `σ = x|_D + C_D`: the number of lanes `j` with
`ℓ_j|_D + C_D = σ`, i.e. `π_D(ℓ_j - x) ∈ C`. -/
noncomputable def cosetCount {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m))
    (ℓ : Fin w → Word m) (x : Word m) : ℕ :=
  (univ.filter fun j => proj D (ℓ j - x) ∈ C).card

/-- The observable profile `T_C(ℓ) = (n_{D,σ}(ℓ))_{D,σ}`: block coset counts on every block of
`B_C`, cosets indexed by representatives. -/
noncomputable def profile {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ : Fin w → Word m) :
    ↥(blocks C) → Word m → ℕ :=
  fun D x => cosetCount C D.1 ℓ x

/-- `n_A(ℓ) = |{j : A · ℓ_j = 1}|`. -/
noncomputable def charCount {w : ℕ} (A : Word m) (ℓ : Fin w → Word m) : ℕ :=
  (univ.filter fun j => dotProduct A (ℓ j) = 1).card

/-- The signed character count `n̂_A(ℓ) = w - 2 n_A(ℓ)` (an integer). -/
noncomputable def hatCount {w : ℕ} (A : Word m) (ℓ : Fin w → Word m) : ℤ :=
  (w : ℤ) - 2 * (charCount A ℓ : ℤ)

/-- Each aggregate coordinate `∑_j Y_{j,e}` (integer sum of bits) is at most `w`. -/
theorem aggregate_le {w : ℕ} (Y : Fin w → Word m) (e : Fin m) :
    ∑ j, (Y j e).val ≤ w := by
  calc ∑ j, (Y j e).val ≤ ∑ _j : Fin w, 1 :=
        Finset.sum_le_sum fun j _ => Nat.lt_succ_iff.mp (ZMod.val_lt (Y j e))
    _ = w := by simp

/-- The observation `H_e = ∑_j Y_{j,e}`, with representatives `0, 1` and integer addition:
a labelled vector in `{0,…,w}^m`. -/
def aggregate {w : ℕ} (Y : Fin w → Word m) : Fin m → Fin (w + 1) :=
  fun e => ⟨∑ j, (Y j e).val, Nat.lt_succ_of_le (aggregate_le Y e)⟩

/-- The law `P_ℓ` of one observation: masks `U_j` independent and uniform on `C`,
`Y_j = ℓ_j + U_j` (binary addition), `H = aggregate Y`. `P_ℓ(h)` is the fraction of mask
tuples `(U_1,…,U_w) ∈ C^w` producing `h`. -/
noncomputable def law {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ : Fin w → Word m) :
    (Fin m → Fin (w + 1)) → ℝ :=
  fun h => ((univ.filter fun U : Fin w → ↥C =>
      aggregate (fun j => ℓ j + (U j : Word m)) = h).card : ℝ) /
    (Fintype.card ↥C : ℝ) ^ w

/-- `B`: the product of `m` independent `Bin(w, 1/2)` laws. -/
noncomputable def binomProd (w : ℕ) : (Fin m → Fin (w + 1)) → ℝ :=
  fun h => ∏ e, ((w.choose (h e : ℕ) : ℝ) / 2 ^ w)

/-- The coordinatewise Krawtchouk product `ψ_r(h) = ∏_e K_{r_e}(h_e)` of width `w`, with
`∑_j K_j(h) z^j = (1 - z)^h (1 + z)^{w - h}`; `K` is the published `MatousekLP.Codes.K w t h`.
For `r_e > w` the factor is `0` (zero extension). -/
noncomputable def psi (w : ℕ) (r : Fin m → ℕ) (h : Fin m → Fin (w + 1)) : ℤ :=
  ∏ e, MatousekLP.Codes.K w (r e) (h e : ℕ)

/-- `|r| = ∑_e r_e`. -/
def absIdx (r : Fin m → ℕ) : ℕ := ∑ e, r e

/-- The multi-binomial `binom(w, r) = ∏_e binom(w, r_e)`. -/
def multiBinom (w : ℕ) (r : Fin m → ℕ) : ℕ := ∏ e, w.choose (r e)

/-- The multi-indices `r ∈ {0,…,w}^m`. -/
def lowIndices (m w : ℕ) : Finset (Fin m → ℕ) := Fintype.piFinset fun _ => range (w + 1)

/-- The moment `c_ℓ(r) = E_ℓ ψ_r(H)`. -/
noncomputable def moment {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ : Fin w → Word m)
    (r : Fin m → ℕ) : ℝ :=
  ∑ h, law C ℓ h * (psi w r h : ℝ)

/-- `s(ℓ, ℓ′) = min{|r| : c_ℓ(r) ≠ c_{ℓ′}(r)}` (`⊤` when all moments agree). -/
noncomputable def momentOrder {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ ℓ' : Fin w → Word m) :
    ℕ∞ :=
  ⨅ (r : Fin m → ℕ) (_ : moment C ℓ r ≠ moment C ℓ' r), (absIdx r : ℕ∞)

/-- Profiles are parity-equivalent when `n_A(ℓ) ≡ n_A(ℓ′) (mod 2)` for every dual word `A`
(the observable parities `∑_{e ∈ A} H_e ≡ n_A (mod 2)` agree). -/
def ParityEquivalent {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ ℓ' : Fin w → Word m) : Prop :=
  ∀ A ∈ dualCode C, charCount A ℓ % 2 = charCount A ℓ' % 2

/-- The observable parity class of `ℓ`: the `h ∈ {0,…,w}^m` with
`∑_{e ∈ A} h_e ≡ n_A(ℓ) (mod 2)` for every dual word `A`. -/
noncomputable def parityClass {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ : Fin w → Word m) :
    Finset (Fin m → Fin (w + 1)) :=
  univ.filter fun h => ∀ A ∈ dualCode C, (∑ e ∈ supp A, (h e : ℕ)) % 2 = charCount A ℓ % 2

/-- `B_ℓ`: the law `B` conditioned on the observable parity class of `ℓ`. -/
noncomputable def condBinom {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ : Fin w → Word m) :
    (Fin m → Fin (w + 1)) → ℝ :=
  fun h => if h ∈ parityClass C ℓ then
    binomProd w h / ∑ h' ∈ parityClass C ℓ, binomProd w h' else 0

/-- `M`-balance: `|n_{D,σ} - w/|Q_D|| ≤ M` for every block coset. -/
def IsBalanced {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (M : ℝ) (ℓ : Fin w → Word m) : Prop :=
  ∀ D ∈ blocks C, ∀ x : Word m, |(cosetCount C D ℓ x : ℝ) - (w : ℝ) / numCosets C D| ≤ M

/-- `α`-density: every block-coset count is at least `α w`. -/
def IsDense {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (α : ℝ) (ℓ : Fin w → Word m) : Prop :=
  ∀ D ∈ blocks C, ∀ x : Word m, α * (w : ℝ) ≤ (cosetCount C D ℓ x : ℝ)

/-- The joint cumulant `κ_C(A)` of the spins `((-1)^{U_e})_{e ∈ A}`, `U ∼ Unif(C)`, given by the
moment–cumulant partition formula (the published `AMPLowDeg.RankOne.cum`). -/
noncomputable def spinCumulant (C : Submodule (ZMod 2) (Word m)) (A : Word m) : ℝ :=
  letI : MeasurableSpace ↥C := ⊤
  AMPLowDeg.RankOne.cum (PMF.uniformOfFintype ↥C).toMeasure
    (fun (e : ↥(supp A)) (U : ↥C) => (-1 : ℝ) ^ ((U : Word m) e.1).val)

end AggregatedCodeTesting.Testing


