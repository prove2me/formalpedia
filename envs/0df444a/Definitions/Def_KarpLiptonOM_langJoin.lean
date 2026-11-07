-- Prove2me | Definitions.Def_KarpLiptonOM_langJoin
-- name    : KarpLiptonOM_langJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:20.010446+00:00
-- url     : https://prove2.me/theorems/e1ad281c-ac0b-4804-8a03-7c491bd02b09
-- title:
--   Join $A_1 \oplus \cdots \oplus A_r$ of languages
-- statement:
--   For languages $A_1, \dots, A_r$, the join is the language $\{\langle i, q\rangle : q \in A_i\}$, the yes-part of the join of the promise problems $(A_i, \overline{A_i})$. A machine with oracles $A_1, \dots, A_r$ is a machine with this single oracle, so $\mathrm P^{A_1, \dots, A_r}$ means $\mathrm P^{A_1 \oplus \cdots \oplus A_r}$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21; Lemma A.3.1, p.25

import Mathlib
import Definitions.Def_KarpLiptonOM_promiseJoin
import Definitions.Def_KarpLiptonOM_toPromise

namespace KarpLiptonOM

/-- The join `A₁ ⊕ ⋯ ⊕ A_r` of languages, `{⟨i, q⟩ : q ∈ A_i}` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21, the join of the
promise problems `(A_i, Ā_i)`). `P^{A₁,…,A_r}` is `P` with this single oracle. -/
def langJoin {r : ℕ} (A : Fin r → Set (List Bool)) : Set (List Bool) :=
  (promiseJoin (fun i => toPromise (A i))).yes

end KarpLiptonOM


