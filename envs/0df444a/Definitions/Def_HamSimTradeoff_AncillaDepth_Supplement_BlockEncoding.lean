-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_BlockEncoding
-- name    : HamSimTradeoff_AncillaDepth_Supplement_BlockEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:52.620052+00:00
-- url     : https://prove2.me/theorems/b02e2147-2bbf-40d1-8e3e-491e311197cd
-- title:
--   Single-ancilla evolution circuits using the shared block encoding
-- statement:
--   The published general predicate QAlgorithms.IsBlockEncoding is reused: a unitary $U$ on $\mathbb C^{2^a}\otimes\mathbb C^N$ is an $(\alpha,a,\varepsilon)$-block encoding of $A$ when
--   $$\|A-\alpha\langle0^a|U|0^a\rangle\|\le\varepsilon.$$
--   A single-ancilla evolution circuit stores a query count $q$, $q+1$ one-qubit unitaries and a choice at each query between $c_0-e^{iA}$ and $c_1-e^{-iA}$. Evaluation multiplies these gates in their actual order. If a query has depth $d$, the counted depth is $dq+q+1$. The general predicate is imported from the published block-encoding layer; this new module defines only the evolution-circuit data and evaluation, with no error or complexity guarantee.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), pp. 30–31, Definition 6.1, Lemma 6.2, Theorem 6.4

import Definitions.Def_HamSimTradeoff_AncillaDepth_Architecture
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

/-- False = c_0-U; true = c_1-U†. Both are one query. -/
structure EvolutionCircuit where
  q : ℕ
  gates : Fin (q+1) → Matrix.unitaryGroup (Fin 2) ℂ
  inverseQuery : Fin q → Bool

def evolutionQuery {N : ℕ} (A : Mat N) (inverse : Bool) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  if inverse then Matrix.kronecker (Matrix.diagonal ![1,0]) (1 : Mat N) +
    Matrix.kronecker (Matrix.diagonal ![0,1]) (evolution A 1)
  else Matrix.kronecker (Matrix.diagonal ![1,0]) (evolution A (-1)) +
    Matrix.kronecker (Matrix.diagonal ![0,1]) (1 : Mat N)

def evolutionCircuit {N : ℕ} (B : EvolutionCircuit) (A : Mat N) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  ((List.finRange B.q).reverse.map (fun j =>
    Matrix.kronecker (B.gates ⟨j.val+1, by omega⟩ : Mat 2) (1 : Mat N) *
      evolutionQuery A (B.inverseQuery j))).prod *
    Matrix.kronecker (B.gates ⟨0, by omega⟩ : Mat 2) (1 : Mat N)

def evolutionDepth (B : EvolutionCircuit) (d : ℕ) : ℕ := d*B.q + B.q+1

end
end HamSimTradeoff.AncillaDepth.Supplement


