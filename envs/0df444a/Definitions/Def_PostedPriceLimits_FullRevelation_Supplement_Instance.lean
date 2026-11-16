-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_Instance
-- name    : PostedPriceLimits_FullRevelation_Supplement_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:08:57.366359+00:00
-- url     : https://prove2.me/theorems/01cbdee6-976f-422a-8498-b789ffbc29f2
-- title:
--   The complete §4 single-query hard distribution and oracle
-- statement:
--   For a positive integer $n$, define the §4 parameters
--
--   $$\kappa=2^{20n},\quad\beta=\kappa^\kappa,\quad\lambda=\beta^\kappa,\quad\operatorname{val}(k)=\beta^k,\quad\operatorname{num}(k)=\lambda/\beta^k\quad(1\le k\le\kappa).$$
--
--   A private label is $(j,k,r,\ell)$ with owner $j\in[n]$, rank $k\in[\kappa]$, role vector $r\in\{-\kappa,\ldots,\kappa\}^n$ and layer $\ell\in[\kappa\operatorname{num}(k)]$. Each label has exactly $\lambda^{10}$ item copies. A uniformly random permutation assigns these labelled copies to the ordered items. Independently, each bidder has a uniform real offset $\theta_i\in[0,1]$. The exact number of items is
--
--   $$m(n)=n\kappa\lambda^{10}(2\kappa+1)^n\sum_{k=1}^{\kappa}\operatorname{num}(k).$$
--
--   An $i$-slice fixes a different owner and all role coordinates except $i$. A matrix has $\kappa$ rows and columns and entries in $\{0,\ldots,\kappa\}$. Its information depth $s(Q)$ is the least $s\ge0$ such that rows are equal within each part of the published rank partition $\mathcal K_s$. Set $\operatorname{rank}(k,Q)=\min\mathcal K_{s(Q)+1}(k)$. A clause list $A$ assigns a matrix $A_\sigma$ to every $i$-slice; the representation contains every such list.
--
--   For an item $(i,k,r,\ell)$ owned by bidder $i$, its coefficient is $\beta^{1/2}\operatorname{val}(k)$ when $r=0$, and zero otherwise. For a non-owner item in slice $\sigma$, its coefficient is $\operatorname{val}(\operatorname{rank}(k,A_\sigma))$ if $r_i=0$; $\operatorname{val}(-r_i)$ if $-r_i\in[k]\setminus\{\operatorname{rank}(k,A_\sigma)\}$; $\operatorname{val}(r_i)-1+\mathbf1\{\ell\le A_{\sigma,k,r_i}\}$ if $r_i,\ell\in[\kappa]$; and zero otherwise. The bias is
--
--   $$u_0^{(i,A)}=\lambda^{10}\bigl(\lambda-\kappa|\Sigma_i|\operatorname{Avg}[\theta_i A+A^2/2]\bigr),\qquad v_i(S)=\max_A\bigl(u^{(i,A)}(S)+u_0^{(i,A)}\mathbf1\{S\ne\varnothing\}\bigr).$$
--
--   The bias is nonnegative in the sufficiently large regime. The average is uniform over all slice, row and column entries. The published biased clause value and lexicographic demand functions are reused. Empty demand returns the zero clause. On nonempty demand, the selected supporting list minimizes the lexicographic ordinary clause produced by Proposition 3.8 at the greatest demanded item. Thus its deterministic tie rule implements the published simulation, while its list index stays private.
--
--   The ordinary family is computed from every biased clause $u$ and pivot $z$: coefficient $u_x$ for $x<z$, $u_z+u_0$ at $z$, and zero for $x>z$, together with the zero clause. The conversion predicate requires exact equality with this full computed family. This provides the ordinary represented profiles used in the lower bound; no arbitrary low-welfare certificate is an input.
--
--   **Formalization Note** The item type is `Fin` of the cardinality of all labelled copies. Theorem 2.1 also asserts equality with the displayed count formula, its $\lambda^{12}$ upper bound, and $\log_2\log_2 m(n)=\Theta(n)$. Rank and layer coordinates add one to their `Fin` values; roles subtract $\kappa$. Natural division is exact on $1\le k\le\kappa$. Values outside the offset support are not used for pointwise claims. No §5 construction is imported.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), §4–§4.1, pp.8–9 (PDF 9–10); computed ordinary conversion from Proposition 3.8, p.6 (PDF 7)

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_SingleQuery
import Definitions.Def_PostedPriceLimits_FullRevelation_Prelim

set_option autoImplicit false
open MeasureTheory
open ComplementFreeCA.XOSGreedy
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation.Supplement

noncomputable section

def kappa (n : ℕ) : ℕ := 2 ^ (20 * n)
def beta (n : ℕ) : ℕ := kappa n ^ kappa n
def lam (n : ℕ) : ℕ := beta n ^ kappa n
def value (n k : ℕ) : ℝ := (beta n : ℝ) ^ k
def num (n k : ℕ) : ℕ := lam n / beta n ^ k

abbrev Rank (n : ℕ) := Fin (kappa n)
abbrev Role (n : ℕ) := Fin (2 * kappa n + 1)
def roleInt {n : ℕ} (r : Role n) : ℤ := (r.val : ℤ) - kappa n

/-- All private labels; Fin coordinates encode the source's one-based indices. -/
abbrev Label (n : ℕ) :=
  (_j : Fin n) × (k : Rank n) × ((Fin n → Role n) × Fin (kappa n * num n (k.val + 1)))
abbrev Atom (n : ℕ) := Label n × Fin (lam n ^ 10)
def itemCount (n : ℕ) : ℕ := Fintype.card (Atom n)
def countFormula (n : ℕ) : ℕ :=
  n * kappa n * lam n ^ 10 * (2 * kappa n + 1) ^ n * ∑ k ∈ rankRange (kappa n), num n k
abbrev Item (n : ℕ) := Fin (itemCount n)

/-- A uniformly random permutation of the full set of labelled copies. -/
abbrev Draw (n : ℕ) := Equiv.Perm (Atom n) × (Fin n → ℝ)
instance permFintype (n : ℕ) : Fintype (Equiv.Perm (Atom n)) := Fintype.ofFinite _
instance permMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Atom n)) := ⊤

def drawLaw (n : ℕ) : Measure (Draw n) :=
  (PMF.uniformOfFintype (Equiv.Perm (Atom n))).toMeasure.prod (Measure.pi (fun _ : Fin n => unitUniform))

def labelAt {n : ℕ} (ω : Draw n) (x : Item n) : Label n :=
  (ω.1 ((Fintype.equivFin (Atom n)).symm x)).1

def fiber {n : ℕ} (ω : Draw n) (L : Label n) : Finset (Item n) :=
  Finset.univ.filter (fun x => labelAt ω x = L)

/-- An i-slice has a different owner and all role coordinates except i. -/
abbrev Slice (n : ℕ) (i : Fin n) := {j : Fin n // j ≠ i} × ({j : Fin n // j ≠ i} → Role n)
abbrev Matrix (n : ℕ) := Rank n → Rank n → Fin (kappa n + 1)
abbrev ClauseList (n : ℕ) (i : Fin n) := Slice n i → Matrix n

def sliceOf {n : ℕ} (i : Fin n) (L : Label n) (h : L.1 ≠ i) : Slice n i :=
  (⟨L.1, h⟩, fun j => L.2.2.1 j.1)

def rowsConstant {n : ℕ} (A : Matrix n) (s : ℕ) : Prop :=
  ∀ k r : Rank n, partOf (rankPartition (kappa n) s) (k.val + 1) =
    partOf (rankPartition (kappa n) s) (r.val + 1) → A k = A r

/-- Least depth; the set is nonempty because iterated partitions eventually are singletons. -/
def depth {n : ℕ} (A : Matrix n) : ℕ := sInf {s | rowsConstant A s}
def roundedRank {n : ℕ} (k : Rank n) (A : Matrix n) : ℕ :=
  sInf (↑(partOf (rankPartition (kappa n) (depth A + 1)) (k.val + 1)) : Set ℕ)

def coefficient {n : ℕ} (ω : Draw n) (i : Fin n) (A : ClauseList n i) (x : Item n) : ℝ :=
  let L := labelAt ω x
  let k := L.2.1
  let r := L.2.2.1
  let ell := L.2.2.2.val + 1
  if h : L.1 = i then
    if ∀ j, roleInt (r j) = 0 then Real.sqrt (beta n) * value n (k.val + 1) else 0
  else
    let Q := A (sliceOf i L h)
    let ri := roleInt (r i)
    if ri = 0 then value n (roundedRank k Q)
    else if 1 ≤ -ri ∧ -ri ≤ k.val + 1 ∧ (-ri).toNat ≠ roundedRank k Q then value n (-ri).toNat
    else if hr : 1 ≤ ri ∧ ri ≤ kappa n then
      if ell ≤ kappa n then
        value n ri.toNat - 1 +
          if ell ≤ (Q k ⟨ri.toNat - 1, by omega⟩).val then 1 else 0
      else 0
    else 0

def bias {n : ℕ} (ω : Draw n) (i : Fin n) (A : ClauseList n i) : ℝ :=
  (lam n : ℝ) ^ 10 * ((lam n : ℝ) - kappa n * Fintype.card (Slice n i) *
    avg (Finset.univ : Finset (Slice n i × Rank n × Rank n))
      (fun t => ω.2 i * (A t.1 t.2.1 t.2.2).val + ((A t.1 t.2.1 t.2.2).val : ℝ) ^ 2 / 2))

def biasedClause {n : ℕ} (ω : Draw n) (i : Fin n) (A : ClauseList n i) : ℝ × (Item n → ℝ) :=
  (bias ω i A, coefficient ω i A)

def fullClauses {n : ℕ} (ω : Draw n) (i : Fin n) : Finset (ℝ × (Item n → ℝ)) :=
  Finset.univ.image (biasedClause ω i)

def valuation {n : ℕ} (ω : Draw n) (i : Fin n) (S : Finset (Item n)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun A : ClauseList n i => biasedClauseValue (biasedClause ω i A) S)

/-- Proposition 3.8's computed ordinary additive clauses, at z=max S. -/
def truncated {n : ℕ} (c : ℝ × (Item n → ℝ)) (z : ℕ) : Item n → ℝ :=
  fun x => if x.val < z then c.2 x else if x.val = z then c.2 x + c.1 else 0

/-- Deterministic supporting-clause selection implementing Proposition 3.8's simulation:
minimize the ordinary returned additive clause, never disclose the list index. -/
def responseList {n : ℕ} (ω : Draw n) (i : Fin n) (p : Item n → ℝ≥0∞) : ClauseList n i :=
  let S := demandSet (valuation ω i) p
  let C := (Finset.univ : Finset (ClauseList n i)).filter
    (fun A => biasedClauseValue (biasedClause ω i A) S = valuation ω i S)
  if h : C.Nonempty then Classical.choose
    (C.exists_min_image (fun A => toLex (truncated (biasedClause ω i A) (S.sup Fin.val))) h)
  else fun _ _ _ => 0

def biasedOracle {n : ℕ} (ω : Draw n) (i : Fin n) (p : Item n → ℝ≥0∞) :
    Finset (Item n) × (ℝ × (Item n → ℝ)) :=
  let S := demandSet (valuation ω i) p
  (S, if S = ∅ then 0 else biasedClause ω i (responseList ω i p))

def ordinaryClauses {n : ℕ} (ω : Draw n) (i : Fin n) : Finset (Item n → ℝ) :=
  insert 0 (Finset.univ.image (fun t : ClauseList n i × Item n => truncated (biasedClause ω i t.1) t.2.val))

/-- An ordinary represented profile with exactly the full converted clause families.
This is a predicate on the computed families, not a free surrogate valuation. -/
def IsConverted {n : ℕ} (ω : Draw n) (E : Fin n → XOSExpr (itemCount n)) : Prop :=
  ∀ i, (E i).clauses = ordinaryClauses ω i

end
end PostedPriceLimits.FullRevelation.Supplement


