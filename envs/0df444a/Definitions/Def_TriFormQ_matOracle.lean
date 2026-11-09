-- Prove2me | Definitions.Def_TriFormQ_matOracle
-- name    : TriFormQ_matOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:37.508437+00:00
-- url     : https://prove2.me/theorems/88eb2829-65e9-4cd2-91db-7d05970d3b29
-- title:
--   Matrix–vector multiplication oracle (RightMult and LeftMult)
-- statement:
--   For $M\in M_n(\mathbb F)$, the black-box access of Lemma 5 consists of two kinds of classical queries:
--
--   $$\mathrm{RightMult}:\ y\mapsto My,\qquad \mathrm{LeftMult}:\ x\mapsto x^\top M,\qquad x,y\in\mathbb F^n .$$
--
--   This definition packages them as one input function on the index set $\mathbb F^n\sqcup\mathbb F^n$ (left copy: RightMult at $y$; right copy: LeftMult at $x$), on which the platform's classical decision trees run.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 5, p.17 (PDF p.20)

import Definitions.Def_TriFormQ_TriForm
open Matrix

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 5, p.17 (PDF p.20): "The
only access to M is through matrix-vector multiplication queries RightMult : 𝔽_q^n → 𝔽_q^n,
y ↦ My and LeftMult : 𝔽_q^n → 𝔽_q^n, x ↦ xᵀM."

**Formalization Note.** A classical input `Vec F n ⊕ Vec F n → Vec F n` for the platform's
decision trees `QAlgorithms.DecisionTree`: index `Sum.inl y` is the RightMult query at `y`
(answer `M *ᵥ y`), index `Sum.inr x` is the LeftMult query at `x` (answer `x ᵥ* M`). -/
def matOracle {F : Type} [Field F] {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    Vec F n ⊕ Vec F n → Vec F n
  | Sum.inl y => M *ᵥ y
  | Sum.inr x => x ᵥ* M

end TriFormQ


