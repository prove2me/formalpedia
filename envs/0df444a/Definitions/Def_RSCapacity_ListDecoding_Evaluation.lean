-- Prove2me | Definitions.Def_RSCapacity_ListDecoding_Evaluation
-- name    : RSCapacity_ListDecoding_Evaluation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:56.816707+00:00
-- url     : https://prove2.me/theorems/4d0fbd0c-0f78-4aea-ba7a-53bc6ef2ec13
-- title:
--   RS evaluation, exact polynomial output and agreement cutoffs
-- statement:
--   Let $F$ be a finite field, let $k,n$ be positive integers, and let $\alpha:[n]\to F$ and $y:[n]\to F$ be evaluation points and a received word. The evaluation vector of $f\in F[X]$ is $(f(\alpha_i))_i$, and
--   $$\operatorname{agr}_{\alpha}(f,y)=|\{i\in[n]:f(\alpha_i)=y_i\}|,\qquad
--   \mathcal L_{k,A}(\alpha,y)=\{f\in F[X]:\deg f<k,\ \operatorname{agr}_{\alpha}(f,y)\ge A\}.$$
--   Inputs are the field descriptor, $k,n,A$, and the two vectors, with each field element encoded by its public label. Exact polynomial output means a list without repetitions whose membership is precisely the specified polynomial predicate. Each polynomial is encoded by its $k$ coefficients, padded with zeros; the zero polynomial is included by the strict degree convention.
--
--   The real-parameter specialization uses
--   $$A_{\varepsilon}(k,n)=\min\{n+1,\lceil k(1+\varepsilon)\rceil\}.$$
--   This is a mathematical specification of a supplied integer cutoff. It does not assert that arbitrary real numbers have finite encodings or that a program computes this ceiling from a real oracle. Because agreements are integers at most $n$, this cutoff preserves the exact source output, including the empty-output case.
--
--   The evaluation layer imposes no $k\le n$, no preferred evaluation set and no nonzero multiplier. Injectivity, positivity and characteristic assumptions belong explicitly in the theorem, so this definition adds no hidden instance restrictions.
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), §1 pp.1–2; §2 p.7; Algorithm 1 p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Binary

namespace RSCapacity.ListDecoding

variable {F : Type} [Field F] [Fintype F]

def evaluation {n : ℕ} (α : Fin n → F) (f : Polynomial F) : Fin n → F :=
  fun i => f.eval (α i)

noncomputable def agreement {n : ℕ} (α y : Fin n → F) (f : Polynomial F) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => evaluation α f i = y i).card

def decodingTarget {n : ℕ} (k A : ℕ) (α y : Fin n → F) (f : Polynomial F) : Prop :=
  f.degree < (k : WithBot ℕ) ∧ A ≤ agreement α y f

/-- An exact finite output, without duplicate messages. All coefficient lists
are padded to k, including the zero polynomial; equality is polynomial equality. -/
def polynomialOutput (P : FieldPresentation F) (k : ℕ)
    (target : Polynomial F → Prop) (out : Bits) : Prop :=
  ∃ fs : List (Polynomial F), fs.Nodup ∧
    (∀ f ∈ fs, f.degree < (k : WithBot ℕ)) ∧
    out = encodeList (fun f =>
      (List.ofFn fun i : Fin k => P.encodeElement (f.coeff i.val)).flatten) fs ∧
    ∀ f : Polynomial F, f ∈ fs ↔ target f

def decoderInput (P : FieldPresentation F) (k n A : ℕ) (α y : Fin n → F) : Bits :=
  P.encode ++ encodeNat k ++ encodeNat n ++ encodeNat A ++
    (List.ofFn fun i : Fin n => P.encodeElement (α i)).flatten ++
    (List.ofFn fun i : Fin n => P.encodeElement (y i)).flatten

/-- This is a specification, never a proposed computation on arbitrary reals. -/
noncomputable def realCutoff (k n : ℕ) (ε : ℝ) : ℕ :=
  min (n + 1) ⌈(k : ℝ) * (1 + ε)⌉₊

end RSCapacity.ListDecoding


