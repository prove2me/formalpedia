-- Prove2me | Definitions.Def_QBFBackdoor_encCNF
-- name    : QBFBackdoor_encCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:32.754027+00:00
-- url     : https://prove2.me/theorems/34407353-344a-4402-b1a3-201ecc110fd5
-- title:
--   Instances and their bit encodings
-- statement:
--   The decision problems of the mission take their instances as bit strings. Four instance types are used:
--
--   1. a CNF QBF $(n,m,\Phi)$, and the same with a supplied variable set $B$;
--   2. a guarded-affine QBF $(n,m,\Psi)$, and the same with a supplied variable set $B$;
--   3. a disjunctive QBF over $\Gamma_{\mathrm{AFF}}$, $(n,\Phi)$.
--
--   Each is encoded structurally: $n$ (and $m$) in unary, the $n$ prefix bits, then every clause or atom. A clause, guard or variable set is written as its characteristic vector, a $\Gamma_{\mathrm{AFF}}$ atom as a tag bit followed by its variables in unary, and lists are self-delimiting. For a CNF QBF the length is exactly
--
--   $$
--   (n+1)+(m+1)+n+m(2n+1)+1 .
--   $$
--
--   Every encoding is injective and of length polynomial in the length $\lVert\Phi\rVert$ of the explicit representation, since $\lVert\Phi\rVert\ge n$ and $\lVert\Phi\rVert\ge m$. None of them carries information about the truth value. This is what makes PSPACE-hardness of the encoded languages a statement about the formulas themselves.
--
--   **Formalization Note** The definitions are `encCNF`, `encCNFB`, `encGAff`, `encGAffB` and `encDQBF`. A verification file proves the injectivity of all five and the length formula above.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §3.1, p.14 (explicit representation, ∥Φ∥)

import Mathlib
import Definitions.Def_QBFBackdoor_IsBackdoor2CNF
import Definitions.Def_QBFBackdoor_DQBF

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved

/-- An instance of QBF (CNF): numbers of variables and clauses, and the formula. -/
structure CNFInst where
  n : ℕ
  m : ℕ
  φ : QBF n m

/-- An instance of QBF (CNF) together with a supplied set of variables (the candidate backdoor). -/
structure CNFInstB where
  n : ℕ
  m : ℕ
  φ : QBF n m
  B : Finset (Fin n)

/-- An instance of QBF with guarded affine atoms. -/
structure GAffInst where
  n : ℕ
  m : ℕ
  ψ : GAffQBF n m

/-- An instance of QBF with guarded affine atoms together with a supplied set of variables. -/
structure GAffInstB where
  n : ℕ
  m : ℕ
  ψ : GAffQBF n m
  B : Finset (Fin n)

/-- Unary, self-delimiting code of a natural number: `k` ones, then a zero. -/
def encNat (k : ℕ) : List Bool :=
  List.replicate k true ++ [false]

/-- Self-delimiting code of a list: each element is preceded by a one, the list ends with a
zero. -/
def encList {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  (l.map (fun a => true :: e a)).flatten ++ [false]

/-- Characteristic vector of a variable set, of length `n`. -/
def encVarSet {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn (fun v : Fin n => decide (v ∈ S))

/-- Characteristic vector of a clause (a set of literals), of length `2n`: first the positive
literals `x_v`, then the negative literals `¬x_v`. -/
def encClause {n : ℕ} (c : Finset (Fin n × Bool)) : List Bool :=
  List.ofFn (fun v : Fin n => decide ((v, true) ∈ c)) ++
    List.ofFn (fun v : Fin n => decide ((v, false) ∈ c))

/-- **Encoding of a CNF QBF instance** as a bit string: `n` and `m` in unary, the `n` prefix bits
(`true` = ∃), then the list of the `m` clauses, each as its characteristic vector.

**Formalization Note** The encoding is structural and injective, and its length
`n + m + 3 + n + m·(2n + 1) + 1` is polynomially related to the length `∥Φ∥` of the explicit
representation (§3.1, p.14), since `∥Φ∥ ≥ n` and `∥Φ∥ ≥ m`. It carries no information about the
truth value. -/
def encCNF (I : CNFInst) : List Bool :=
  encNat I.n ++ encNat I.m ++ List.ofFn I.φ.q ++ encList encClause (List.ofFn I.φ.clause)

/-- Encoding of a CNF QBF instance with a supplied variable set: the encoding of the instance,
followed by the characteristic vector of the set. -/
def encCNFB (I : CNFInstB) : List Bool :=
  encCNF ⟨I.n, I.m, I.φ⟩ ++ encVarSet I.B

/-- Encoding of a guarded affine atom: the characteristic vector of the equation's variables, the
right-hand side, and the characteristic vector of the guard. -/
def encGAffAtom {n : ℕ} (C : GAff n) : List Bool :=
  encVarSet C.eqv ++ [C.rhs] ++ encClause C.guard

/-- **Encoding of a guarded-affine QBF instance**: `n` and `m` in unary, the prefix bits, then the
list of the `m` atoms. Structural and injective, of length polynomial in `∥Φ∥`. -/
def encGAff (I : GAffInst) : List Bool :=
  encNat I.n ++ encNat I.m ++ List.ofFn I.ψ.q ++ encList encGAffAtom (List.ofFn I.ψ.atom)

/-- Encoding of a guarded-affine QBF instance with a supplied variable set. -/
def encGAffB (I : GAffInstB) : List Bool :=
  encGAff ⟨I.n, I.m, I.ψ⟩ ++ encVarSet I.B

/-- Self-delimiting encoding of a `Γ_AFF` atom: a tag bit, then the variable(s) in unary, and for
a unit atom its value. -/
def encGAtom {n : ℕ} : GAtom n → List Bool
  | .unit x b => false :: (encNat x.val ++ [b])
  | .eq x y => true :: (encNat x.val ++ encNat y.val)

/-- **Encoding of a Disjunct-QBF(ΓAFF) instance**: `n` in unary, the prefix bits, then the list of
disjuncts, each a list of atoms. Structural and injective, of length polynomial in `∥Φ∥`
(each atom costs at most `2n + 3` bits). -/
def encDQBF (I : DQBFInst) : List Bool :=
  encNat I.n ++ List.ofFn I.Φ.q ++ encList (encList encGAtom) I.Φ.disj

end QBFBackdoor


