-- Prove2me | Definitions.Def_ZKSheafPCP_LacspParams
-- name    : ZKSheafPCP_LacspParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:16:11.349208+00:00
-- url     : https://prove2.me/theorems/ee939ac4-259a-4ace-8d94-4aa8f5c31eee
-- title:
--   $\mathrm{LACSP}$ and $\mathrm{RLACSP}$, and the family of Theorem 9.7
-- statement:
--   Fix a field $\mathbb F(n)$, linear codes $C_0(n),C_1(n)$ of block length $\ell(n)$ and relative distance at least $\tau(n)$, a locality $q(n)$, and $t(n)$. An **instance** is $x=(1^n,g)$ with $g:\mathbb F(n)^{\ell(n)}\to\mathbb F(n)^{\ell(n)}$ that is $q(n)$-local, $q(n)$-evasive and computable in polynomial time, with $C_1(n)\cup g(C_0(n))$ of relative distance at least $\tau(n)$. The **yes-relation** of RLACSP consists of $t(n)$-randomizable instances with a witness $(w_0,w_1)$, $w_0\in C_0(n)$, $w_1\in C_1(n)$, $g(w_0)=w_1$. An instance is $t(n)$-randomizable if there is a $t(n)$-wise independent subcode $C'\subseteq C_0(n)$ such that if $(c_0,g(c_0))$ satisfies $x$, so does $(c_0',g(c_0'))$ for every $c_0'\in c_0+C'$. The **no-language** consists of instances with no satisfying witness.
--
--   The family of Theorem 9.7 has $\mathbb F(n)$ binary, additive subgroups $H_0\le L$, $C_0=\mathrm{RS}[\mathbb F,L,d_0]$, $C_1$ the subcode of $\mathrm{RS}[\mathbb F,L,d_1]$ vanishing on a coset $H$ of $H_0$ with $H\cap L=\emptyset$, $d_0,d_1\le|L|/8-1$, and $\ell=|L|$.
--
--   **Formalization Note** $g$ is described by an oracle machine with a polynomial clock. The sets of locality and of evasiveness coincide, as in Definition 9.3. Definition 9.6's parameter $c(n)$ is used nowhere, and Theorem 9.7 omits it.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 9.3–9.6, p.43; Theorem 9.7, p.43

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAdvFew_PoQOracle_OTM_code
import Definitions.Def_ZKSheafPCP_RSIndex

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP

open Classical

/-- The parameters of the promise relation `RLACSP[𝔽(n), C₀(n), C₁(n), ℓ(n), τ(n), q(n), t(n)]` (Zeilberger, O'Connor,
Gur, Spooner, STOC 2027 submission, manuscript sha256 ac5e528f…, Definitions 9.4 and 9.6, p.43), with `clock`, the
polynomial in "`g` can be computed in time `poly(n)`".

**Formalization Note** `dec` reads a field element from its symbol in `Fin (a n)`. Definition 9.6 also lists a `c(n)`
that nothing uses, and Theorem 9.7 omits it, so it is left out. -/
structure LacspParams where
  /-- the field `𝔽(n)` -/
  F : ℕ → Type
  [fld : ∀ n, Field (F n)]
  /-- the alphabet size -/
  a : ℕ → ℕ
  /-- the field element of a symbol -/
  dec : ∀ n, Fin (a n) → F n
  /-- symbols are in bijection with the field -/
  hdec : ∀ n, Function.Bijective (dec n)
  /-- the block length -/
  ℓ : ℕ → ℕ
  /-- the code `C₀(n)` -/
  C0 : ∀ n, Submodule (F n) (Fin (ℓ n) → F n)
  /-- the code `C₁(n)` -/
  C1 : ∀ n, Submodule (F n) (Fin (ℓ n) → F n)
  /-- the relative distance -/
  τ : ℕ → ℝ
  /-- the locality and evasiveness -/
  q : ℕ → ℕ
  /-- the randomizability -/
  t : ℕ → ℕ
  /-- the time to compute `g` -/
  clock : ℕ → ℕ

attribute [instance] LacspParams.fld

namespace LacspParams

variable (Λ : LacspParams)

/-- The word over the field of a word over symbols. -/
def word (n : ℕ) (π : Fin (Λ.ℓ n) → Fin (Λ.a n)) : Fin (Λ.ℓ n) → Λ.F n := fun i => Λ.dec n (π i)

/-- A set of words has relative distance at least `τ`: distinct words differ in at least a `τ` fraction of the positions. -/
def HasRelDist (n : ℕ) (W : Set (Fin (Λ.ℓ n) → Λ.F n)) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
    Λ.τ n * Λ.ℓ n ≤ ((Finset.univ.filter fun i => u i ≠ v i).card : ℝ)

/-- "`C₀(n)` and `C₁(n)` … linear codes … with … relative distance `τ(n)`" (Definition 9.4, p.43). -/
def CodesHaveDist : Prop :=
  ∀ n, Λ.HasRelDist n (Λ.C0 n : Set _) ∧ Λ.HasRelDist n (Λ.C1 n : Set _)

/-- The instance string `x = (1ⁿ, g)` with `g` described by an oracle machine (Definition 9.4, p.43). -/
def instEnc (n : ℕ) (M : OTM) : Str := tup [unary n, M.code]

/-- `(1ⁿ, M)` with the function `g` computed by `M` is an instance of LACSP (Definition 9.4, p.43): `M` computes
`g(w)_j` with oracle `w` within `clock n` steps; `g` is `q(n)`-local and `q(n)`-evasive (Definition 9.3); and
`C₁(n) ∪ g(C₀(n))` has relative distance at least `τ(n)`.

**Formalization Note** The sets `I_j` of locality are those of evasiveness. For `m = n = ℓ` the evasiveness bound
`|{j : I_j ∩ I ≠ ∅}|/ℓ ≤ q · |I|/ℓ` of Definition 9.3 is stated with `ℓ` cancelled. -/
structure IsInstance (n : ℕ) (M : OTM) (g : (Fin (Λ.ℓ n) → Λ.F n) → (Fin (Λ.ℓ n) → Λ.F n)) : Prop where
  computes : ∀ (π : Fin (Λ.ℓ n) → Fin (Λ.a n)) (j : Fin (Λ.ℓ n)),
    M.result (proofOracle π) (binN j.val) (Λ.clock n) ≠ none ∧
    ∃ s : Fin (Λ.a n), M.output (proofOracle π) (binN j.val) (Λ.clock n) = binN s.val ∧
      Λ.dec n s = g (Λ.word n π) j
  local_evasive : ∃ I : Fin (Λ.ℓ n) → Finset (Fin (Λ.ℓ n)),
    (∀ j, (I j).card ≤ Λ.q n) ∧
    (∀ j w w', (∀ i ∈ I j, w i = w' i) → g w j = g w' j) ∧
    ∀ I₀ : Finset (Fin (Λ.ℓ n)),
      (Finset.univ.filter fun j => (I j ∩ I₀).Nonempty).card ≤ Λ.q n * I₀.card
  dist : Λ.HasRelDist n ((Λ.C1 n : Set _) ∪ g '' (Λ.C0 n : Set _))

/-- `C'` is `t`-wise independent: on every set of at most `t` positions, a codeword can take any values. For a linear code
this says a uniform codeword is uniform on those positions. -/
def IsTWise (n : ℕ) (C' : Submodule (Λ.F n) (Fin (Λ.ℓ n) → Λ.F n)) : Prop :=
  ∀ I : Finset (Fin (Λ.ℓ n)), I.card ≤ Λ.t n → ∀ u : Fin (Λ.ℓ n) → Λ.F n,
    ∃ c ∈ C', ∀ i ∈ I, c i = u i

/-- `t(n)`-randomizability (Definition 9.5, p.43). -/
def Randomizable (n : ℕ) (g : (Fin (Λ.ℓ n) → Λ.F n) → (Fin (Λ.ℓ n) → Λ.F n)) : Prop :=
  ∃ C' : Submodule (Λ.F n) (Fin (Λ.ℓ n) → Λ.F n), C' ≤ Λ.C0 n ∧ Λ.IsTWise n C' ∧
    ∀ c0 ∈ Λ.C0 n, g c0 ∈ Λ.C1 n → ∀ c' ∈ C', c0 + c' ∈ Λ.C0 n ∧ g (c0 + c') ∈ Λ.C1 n

/-- The code of a word over symbols, as a string. -/
def wordCode {L a : ℕ} (π : Fin L → Fin a) : Str := tup ((List.finRange L).map fun i => binN (π i).val)

/-- `R^YES_RLACSP` (Definitions 9.4, 9.6, p.43): the pairs of a `t(n)`-randomizable instance and a witness `(w₀, w₁)` with
`w₀ ∈ C₀(n)`, `w₁ ∈ C₁(n)`, `g(w₀) = w₁`. -/
def RYes : Set (Str × Str) :=
  {p | ∃ (n : ℕ) (M : OTM) (g : (Fin (Λ.ℓ n) → Λ.F n) → (Fin (Λ.ℓ n) → Λ.F n)),
    p.1 = instEnc n M ∧ Λ.IsInstance n M g ∧ Λ.Randomizable n g ∧
    ∃ π0 π1 : Fin (Λ.ℓ n) → Fin (Λ.a n), p.2 = tup [wordCode π0, wordCode π1] ∧
      Λ.word n π0 ∈ Λ.C0 n ∧ Λ.word n π1 ∈ Λ.C1 n ∧ g (Λ.word n π0) = Λ.word n π1}

/-- `L^NO_RLACSP := L^NO_LACSP` (Definitions 9.4, 9.6, p.43): the instances with no satisfying witness. -/
def LNo : Set Str :=
  {x | ∃ (n : ℕ) (M : OTM) (g : (Fin (Λ.ℓ n) → Λ.F n) → (Fin (Λ.ℓ n) → Λ.F n)),
    x = instEnc n M ∧ Λ.IsInstance n M g ∧ ¬ ∃ c0 ∈ Λ.C0 n, g c0 ∈ Λ.C1 n}

/-- The pair language of the relation `C₀ × C₁` (Theorem 9.8, p.44): the explicit input is `1ⁿ` and the implicit input a pair
`(w₀, w₁)` of words of length `ℓ(n)`. -/
def ccFamily : PCPPFamily where
  Inst := ℕ
  enc n := unary n
  N n := Λ.ℓ n + Λ.ℓ n
  a n := Λ.a n
  Lang n := {y | (fun i => Λ.dec n (y (Fin.castAdd (Λ.ℓ n) i))) ∈ Λ.C0 n ∧
    (fun i => Λ.dec n (y (Fin.natAdd (Λ.ℓ n) i))) ∈ Λ.C1 n}

end LacspParams

/-- The index `n` of a string `(1ⁿ, c)`, and `0` for any other string. It indexes the parameters of the PCP of
Theorem 9.8 (p.44), which are functions of `n`. -/
noncomputable def lacspIndex (x : Str) : ℕ :=
  if h : ∃ (n : ℕ) (c : Str), x = tup [unary n, c] then h.choose else 0

/-- The field, the subspaces and the degrees of Theorem 9.7 (p.43): `𝔽(n)` a binary field, `H₀ ≤ L` additive subgroups (`L` by a
basis, `H₀` by generators), `d₀, d₁ ≤ |L|/8 - 1`, and a coset `H = shift + H₀` with `H ∩ L = ∅`. -/
structure RSData where
  /-- the field -/
  B : ℕ → BinField
  /-- symbols read field elements bijectively -/
  sym_bij : ∀ n, Function.Bijective fun a : Fin (2 ^ (B n).deg) => (B n).sym a.val
  /-- the dimension of `L` -/
  k : ℕ → ℕ
  /-- the basis of `L`, as symbols -/
  basis : ∀ n, Fin (k n) → ℕ
  basis_lt : ∀ n j, basis n j < 2 ^ (B n).deg
  indep : ∀ n, Function.Injective fun T : Finset (Fin (k n)) => ∑ j ∈ T, (B n).sym (basis n j)
  /-- the degree bound of `C₀` -/
  d0 : ℕ → ℕ
  /-- the degree bound of `C₁` -/
  d1 : ℕ → ℕ
  hd0 : ∀ n, 8 * (d0 n + 1) ≤ 2 ^ k n
  hd1 : ∀ n, 8 * (d1 n + 1) ≤ 2 ^ k n
  /-- generators of `H₀`, as symbols -/
  gens : ℕ → List ℕ
  /-- the shift of the coset `H`, as a symbol -/
  shift : ℕ → ℕ

namespace RSData

variable (D : RSData)

/-- The point of `L` at position `p`. -/
noncomputable def pt (n p : ℕ) : (D.B n).F :=
  ∑ j : Fin (D.k n), if p.testBit j.val then (D.B n).sym (D.basis n j) else 0

/-- The subspace `L`. -/
def L (n : ℕ) : Set (D.B n).F := Set.range fun p : Fin (2 ^ D.k n) => D.pt n p.val

/-- The subgroup `H₀`: the subset sums of the generators. -/
def H0 (n : ℕ) : Set (D.B n).F :=
  {x | ∃ T : List ℕ, T.Sublist (D.gens n) ∧ x = (T.map (D.B n).sym).sum}

/-- The coset `H = shift + H₀`. -/
def H (n : ℕ) : Set (D.B n).F := {x | ∃ h ∈ D.H0 n, x = (D.B n).sym (D.shift n) + h}

/-- `H₀ ≤ L` and `H ∩ L = ∅`. -/
def Coset : Prop := ∀ n, D.H0 n ⊆ D.L n ∧ D.H n ∩ D.L n = ∅

/-- The evaluation of a polynomial on `L`. -/
noncomputable def evalL (n : ℕ) :
    Polynomial (D.B n).F →ₗ[(D.B n).F] (Fin (2 ^ D.k n) → (D.B n).F) :=
  LinearMap.pi fun p => Polynomial.leval (D.pt n p.val)

/-- The polynomials vanishing on `H`. -/
def vanish (n : ℕ) : Submodule (D.B n).F (Polynomial (D.B n).F) where
  carrier := {p | ∀ x ∈ D.H n, p.eval x = 0}
  add_mem' := by
    intro a b ha hb x hx
    simp [ha x hx, hb x hx]
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro c a ha x hx
    simp [ha x hx]

/-- The parameters of Theorem 9.7 (p.43): `C₀ = RS[𝔽, L, d₀]`, `C₁` the subcode of `RS[𝔽, L, d₁]` vanishing on the coset `H`,
and `ℓ = |L|`. A codeword of `C₁` is the evaluation on `L` of a polynomial of degree at most `d₁` vanishing on `H`. -/
noncomputable def params (τ : ℕ → ℝ) (q t clock : ℕ → ℕ) : LacspParams where
  F n := (D.B n).F
  a n := 2 ^ (D.B n).deg
  dec n s := (D.B n).sym s.val
  hdec := D.sym_bij
  ℓ n := 2 ^ D.k n
  C0 n := (Polynomial.degreeLE (D.B n).F (D.d0 n : ℕ)).map (D.evalL n)
  C1 n := (Polynomial.degreeLE (D.B n).F (D.d1 n : ℕ) ⊓ D.vanish n).map (D.evalL n)
  τ := τ
  q := q
  t := t
  clock := clock

/-- The string describing `𝔽(n), L, d₀, d₁, H`. -/
noncomputable def encAt (n : ℕ) : Str :=
  tup [binN (D.B n).polyCode,
    tup ((List.finRange (D.k n)).map fun j => binN (D.basis n j)),
    binN (D.d0 n), binN (D.d1 n),
    tup ((D.gens n).map binN),
    binN (D.shift n)]

end RSData

end ZKSheafPCP


