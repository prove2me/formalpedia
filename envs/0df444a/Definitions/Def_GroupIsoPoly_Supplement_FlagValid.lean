-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_FlagValid
-- name    : GroupIsoPoly_Supplement_FlagValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:52.186563+00:00
-- url     : https://prove2.me/theorems/a51d3d48-ac72-4224-8977-2794184a2922
-- title:
--   Correct output of Theorem 5.1: an invariant composition flag with kernel $O_p(H)$ and primitive blocks
-- statement:
--   Let $H\le\mathrm{GL}(d,p)$. The output data consist of a length $\ell$, bases of subspaces $V_0,\dots,V_\ell$ of $\mathbb F_p^d$, and for each composition factor $V_{i}/V_{i-1}$ a number $k_i$ of blocks and bases of subspaces $W_{i,1},\dots,W_{i,k_i}$ with $V_{i-1}\le W_{i,a}\le V_i$. The data are **valid** for $H$ if:
--
--   1. every list is linearly independent;
--   2. $0=V_0<V_1<\cdots<V_\ell=\mathbb F_p^d$;
--   3. every $V_j$ is $H$-invariant and every factor $V_i/V_{i-1}$ is irreducible under $H$ (an **invariant composition flag**);
--   4. an element $h\in H$ acts trivially on the **associated graded space** $\bigoplus_i V_i/V_{i-1}$ if and only if $h\in O_p(H)$;
--   5. for every $i$, the $W_{i,a}/V_{i-1}$ are a direct-sum decomposition of $V_i/V_{i-1}$ into nonzero blocks, every $h\in H$ maps blocks onto blocks, $H$ permutes the blocks transitively, and the setwise stabiliser of each block acts on it irreducibly and linearly primitively.
--
--   This is items 1 and 2 of Theorem 5.1 as a property of the output.
--
--   **Formalization Note** By item 4, $O_p(H)$ acts trivially on each factor and so fixes every block; the permutation action of $G=H/O_p(H)$ on the blocks and its block stabilisers are therefore those of $H$, and item 5 is stated for $H$. Factors are indexed from $0$ in Lean ($V_{i+1}/V_i$ for $i<\ell$).
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §5.1 and Theorem 5.1, pp.41–42 (PDF pp.45–46)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_pCore
import Definitions.Def_GroupIsoPoly_Supplement_LinPrimOn

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

/-- **The output data of Theorem 5.1**: an invariant composition flag and, for each composition
factor, its blocks, all given by lists of vectors of `F_p^d`.

* `ℓ` is the length of the flag and `V j` (`j = 0, …, ℓ`) is a basis of `V_j`;
* for the factor `V_{i+1}/V_i` (`i : Fin ℓ`; the paper's `V_i/V_{i−1}`, indexed from `1`), `k i` is the
  number of blocks and `blk i a` is a basis of the subspace `U` with `V_i ≤ U ≤ V_{i+1}` whose image
  `U/V_i` is the `a`-th block. -/
structure FlagData (p d : ℕ) where
  ℓ : ℕ
  V : Fin (ℓ + 1) → List (Fin d → ZMod p)
  k : Fin ℓ → ℕ
  blk : (i : Fin ℓ) → Fin (k i) → List (Fin d → ZMod p)

/-- The span of a list of vectors. -/
noncomputable def spanL {p d : ℕ} [Fact p.Prime] (l : List (Fin d → ZMod p)) :
    Submodule (ZMod p) (Fin d → ZMod p) :=
  Submodule.span (ZMod p) {v | v ∈ l}

/-- A list of vectors is linearly independent (so it is a basis of its span). -/
def IsBasisList {p d : ℕ} [Fact p.Prime] (l : List (Fin d → ZMod p)) : Prop :=
  LinearIndependent (ZMod p) l.get

/-- **Correctness of the output of Theorem 5.1** for `H ≤ GL(d, p)`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §5.1 and Theorem 5.1, pp.41–42 (PDF pp.45–46): "An
invariant composition flag of H is a sequence of invariant subspaces 0 = V0 < V1 < · · · < Vℓ = F_p^d
such that for any i ∈ [ℓ], Vi/Vi−1 is irreducible under the induced action of H"; "1. An invariant
composition flag … such that the action of H on the associated graded space has kernel Op(H).
2. For each Vi/Vi−1, a direct-sum decomposition into blocks permuted transitively by G = H/Op(H),
with each block stabiliser acting irreducibly and linearly primitively on its block."

`FlagValid H D` says, writing `V_j` for the span of `D.V j` and `W_{i,a}` for the span of
`D.blk i a`:
1. every list is linearly independent (a basis of its span);
2. `V_0 = 0`, `V_ℓ = F_p^d`, and `V_i < V_{i+1}`;
3. every `V_j` is `H`-invariant and every factor `V_{i+1}/V_i` is irreducible under `H`;
4. an element `h ∈ H` acts trivially on the graded space `⊕ V_{i+1}/V_i` (that is,
   `h v − v ∈ V_i` for all `i` and `v ∈ V_{i+1}`) if and only if `h ∈ O_p(H)`;
5. for every `i`, the `W_{i,a}/V_i` form a direct-sum decomposition of `V_{i+1}/V_i` into nonzero
   blocks permuted by `H`, the permutation action is transitive, and for every block the setwise
   stabiliser `{h ∈ H : h(W_{i,a}) = W_{i,a}}` acts on `W_{i,a}/V_i` irreducibly and linearly
   primitively.

**Formalization Note.** By item 4, `O_p(H)` acts trivially on every factor, hence fixes every block;
so the action of `G = H/O_p(H)` on the blocks, its transitivity and its block stabilisers are those of
`H` (the stabiliser in `G` is the image of the stabiliser in `H`), which is how item 5 is stated.
A single block (`k = 1`) is allowed. -/
def FlagValid {p d : ℕ} [Fact p.Prime] (H : Subgroup (GL (Fin d) (ZMod p))) (D : FlagData p d) :
    Prop :=
  (∀ j, IsBasisList (D.V j)) ∧ (∀ i a, IsBasisList (D.blk i a)) ∧
  spanL (D.V 0) = ⊥ ∧ spanL (D.V (Fin.last D.ℓ)) = ⊤ ∧
  (∀ i : Fin D.ℓ, spanL (D.V i.castSucc) < spanL (D.V i.succ)) ∧
  (∀ h ∈ H, ∀ j, gmap h (spanL (D.V j)) ≤ spanL (D.V j)) ∧
  (∀ i : Fin D.ℓ, IrredOn (H : Set (GL (Fin d) (ZMod p))) (spanL (D.V i.castSucc))
    (spanL (D.V i.succ))) ∧
  (∀ (h : GL (Fin d) (ZMod p)) (hh : h ∈ H),
    (∀ i : Fin D.ℓ, ∀ v ∈ spanL (D.V i.succ),
      (h : Matrix (Fin d) (Fin d) (ZMod p)).mulVec v - v ∈ spanL (D.V i.castSucc)) ↔
    (⟨h, hh⟩ : H) ∈ pCore p H) ∧
  ∀ i : Fin D.ℓ,
    IsBlockDecomp (H : Set (GL (Fin d) (ZMod p))) (spanL (D.V i.castSucc)) (spanL (D.V i.succ))
      (fun a => spanL (D.blk i a)) ∧
    (∀ a b, ∃ h ∈ H, gmap h (spanL (D.blk i a)) = spanL (D.blk i b)) ∧
    ∀ a, LinPrimOn {h | h ∈ H ∧ gmap h (spanL (D.blk i a)) = spanL (D.blk i a)}
      (spanL (D.V i.castSucc)) (spanL (D.blk i a))

end Supplement

end GroupIsoPoly


