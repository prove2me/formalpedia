-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Matching
-- name    : CatalyticTreeEval_Main_Matching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:54.786497+00:00
-- url     : https://prove2.me/theorems/e233f293-d660-457e-ba42-3842e6addb34
-- title:
--   Score-restricted matching vectors, canonical residues and uniform printers
-- statement:
--   Let $m>1$, $d,N\in\mathbb N$, and let $U_i,V_i\in(\mathbb Z/m\mathbb Z)^d$ be indexed by $0\le i<N$. The score-restricted predicate adds $0\in S$ and off-diagonal membership in $S$ to the published diagonal-zero/off-diagonal-nonzero matching predicate:
--
--   $$\langle U_i,V_i\rangle=0,\qquad i\ne j\Longrightarrow\langle U_i,V_j\rangle\in S\setminus\{0\}.$$
--
--   The sumset contains all sums of two scores. Noncancellation means that two scores summing to zero must both be zero. For a nonempty list of distinct primes $p_i$ and $m=\prod_i p_i$, the canonical set consists of residues congruent to zero or one modulo every prime. Oddness is a separate condition used only when required.
--
--   A fixed finite printer receives a parameter string, unary $N$, binary indices and modulus, and prints both entire vectors in coordinate order using charged workspace. Individual coordinates can be accessed by streaming this output with a counter; there is no free coordinate oracle. Residues have fixed binary width $\lfloor\log_2(m-1)\rfloor+1$. The variable-prime regime uses $t=\lceil\sqrt{\log_2\ell}\rceil$ and the first $t$ odd primes.
--
--   This layer adds the paper's restrictions without duplicating the published general matching object.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Definitions 2.4, 3.7, 3.9, 3.15; Remark 3.8, printed p. 16 (PDF p. 18); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Resources
import Definitions.Def_MatchVec3_IsMVFamily

set_option autoImplicit false

namespace CatalyticTreeEval.Main

abbrev Vec (m d : ℕ) := Fin d → ZMod m

/-- Only the extra score-set restriction is added to the published matching predicate. -/
def SMatching {m d N : ℕ} (S : Set (ZMod m))
    (U V : Fin N → Vec m d) : Prop :=
  0 ∈ S ∧ MatchVec3.IsMVFamily U V ∧ ∀ i j, i ≠ j → U i ⬝ᵥ V j ∈ S

def sumset {m : ℕ} (S : Set (ZMod m)) : Set (ZMod m) :=
  {a | ∃ x ∈ S, ∃ y ∈ S, a = x + y}

def Noncancelling {m : ℕ} (S : Set (ZMod m)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x + y = 0 → x = 0 ∧ y = 0

/-- CRT residues are tested using the canonical natural representative. Used only at m>1. -/
def canonical {t : ℕ} (p : Fin t → ℕ) (m : ℕ) : Set (ZMod m) :=
  {z | ∀ i, z.val % p i = 0 ∨ z.val % p i = 1}

def PrimeData {t : ℕ} (p : Fin t → ℕ) : Prop :=
  0 < t ∧ (∀ i, Nat.Prime (p i)) ∧ Function.Injective p

def OddPrimeData {t : ℕ} (p : Fin t → ℕ) : Prop :=
  PrimeData p ∧ ∀ i, Odd (p i)

def modulus {t : ℕ} (p : Fin t → ℕ) : ℕ := ∏ i, p i

def primeCode {t : ℕ} (p : Fin t → ℕ) : List Bool :=
  natsCode ((List.finRange t).map p)

def vecCode {m d : ℕ} (v : Vec m d) : List Bool :=
  (List.finRange d).flatMap fun i => bits (Nat.log 2 (m - 1) + 1) (v i).val

/-- Standard printer input includes unary family size and binary indices and modulus. -/
def vectorRequest (params : List Bool) (N i j m : ℕ) : List Bool :=
  listCode params ++ List.replicate N true ++ [false] ++ natsCode [i,j,m]

/-- Printer for an individual member of a uniformly parameterized sequence; M is fixed externally. -/
def VectorAccess {m d N : ℕ} (M : Machine) (params : List Bool)
    (U V : Fin N → Vec m d) (space : ℝ) : Prop :=
  ∀ i j, Prints M (vectorRequest params N i.val j.val m)
    (vecCode (U i) ++ vecCode (V j)) space


end CatalyticTreeEval.Main

namespace CatalyticTreeEval.Main

noncomputable def variablePrimeCount (l : ℕ) : ℕ := ⌈Real.sqrt (log₂ l)⌉₊

noncomputable def firstOddPrimes (t : ℕ) : Fin t → ℕ := fun i => Nat.nth Nat.Prime (i.val + 1)

end CatalyticTreeEval.Main


