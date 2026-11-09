-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Scheme
-- name    : InvariantMoneySecurity_Decomposition_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:19.797143+00:00
-- url     : https://prove2.me/theorems/881033e3-19b2-4a12-a2c9-87d65ffb9efa
-- title:
--   Definition 2.1 — an operational invariant quantum money family
-- statement:
--   An invariant money family supplies the finite ground set, inverse-closed moves, and invariant at each object length, together with uniform polynomial-time preparation of the ground-set superposition. Public serials use a fixed polynomial-width padded encoding. The positive round count $r(n)$ is polynomially bounded and uniformly computable. A move index is its canonical zero-based binary numeral, at the bit width of $|S|$. No polynomial bound is placed on the number of objects or moves. As in Definition 2.1, efficient execution of Algorithm 1 is not a component of a scheme; the verifier enters through its effect, equation (5).
--
--   Genuine polynomial-time Turing computations evaluate the invariant and each indexed move and inverse on valid inputs. Their request codes contain the unary security parameter, the binary index, and the object description. These are computational properties of the concrete data; no spectral estimate or adversary reduction is included as a field.
--
--   The family mixes rapidly exactly when
--   $$\exists N\;\forall n\ge N,\qquad r(n)\Delta(n)\ge n.$$
--   The source starts at $n=1$; a dummy value at zero permits ordinary natural-number indexing and affects no negligible-function assertion. A polynomial public serial width is a reversible padding convention. Permitting a uniformly computable polynomially bounded round function includes the source's polynomial round counts and uses the same finite-round verifier.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 6–8, Definition 2.1 and Algorithm 1; p. 11, Definition 3.5

import Definitions.Def_InvariantMoneySecurity_Decomposition_FiniteScheme
import Definitions.Def_InvariantMoneySecurity_Decomposition_UniformCircuits
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition

/-- Definition 2.1 as concrete uniform algorithm families.
At n=0 the data are an arbitrary harmless extension of the source's n≥1 family.
Neither a gap bound nor a preparation/transfer reduction is a scheme field.
A move index is its binary numeral at the width of |S|, so "polynomial time from (i,x)" is
polynomial in the length of (i,x), with no bound on |S|. As in Definition 2.1, efficient
execution of Algorithm 1 is not a component of a scheme. -/
structure Scheme where
  data : ∀ n, FiniteScheme n
  serialPadding : Polynomial ℕ
  serial_width : ∀ n, (data n).serialBits = serialPadding.eval n
  rounds : ℕ → ℕ
  rounds_pos : ∀ n, 1 ≤ rounds n
  rounds_poly : ∃ q : Polynomial ℕ, ∀ n, rounds n ≤ q.eval n
  rounds_computable : ∃ f : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable f ∧ ∀ n, f (codeNat n) = codeNat (rounds n)
  ground_prepared : Prepares (fun n => n) (fun n => uniformVector (data n).ground)
  indexBits : ℕ → ℕ
  index : ∀ n, Fin (data n).moveCount ↪ Bits (indexBits n)
  index_binary : ∀ n j k, index n j k = decide ((j.val / 2 ^ k.val) % 2 = 1)
  index_width : ∀ n, indexBits n = Nat.size (data n).moveCount
  invariant_computable : ∃ f : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ n (x : (data n).Object),
      f (codeNat n ++ codeBits (List.ofFn x.val)) = List.ofFn ((data n).invariant x)
  moves_computable : ∃ f g : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable f ∧
    QAlgorithms.Complexity.PolyTimeComputable g ∧
    ∀ n (j : Fin (data n).moveCount) (x : (data n).Object),
      let request := codeNat n ++ codeBits (List.ofFn (index n j)) ++ codeBits (List.ofFn x.val)
      f request = List.ofFn ((data n).move j x).val ∧
      g request = List.ofFn (((data n).move j).symm x).val

/-- Definition 3.5 includes an eventual threshold, not an all-n promise. -/
def Scheme.RapidMixing (D : Scheme) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ≤ (D.rounds n : ℝ) * (D.data n).gap

end InvariantMoneySecurity.Decomposition


