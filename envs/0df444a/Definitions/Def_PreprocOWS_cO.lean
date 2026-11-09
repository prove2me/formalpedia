-- Prove2me | Definitions.Def_PreprocOWS_cO
-- name    : PreprocOWS_cO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:22:32.638082+00:00
-- url     : https://prove2.me/theorems/a8d52170-95a8-4135-bfac-638bab25c892
-- title:
--   Compressed phase oracle $\mathsf{cO}$ and the compressed run $(\mathsf{cO}\,U)^T$
-- statement:
--   The **compressed phase oracle** of an algorithm with query map $q$ acts on $\mathbb C^{\Omega}\otimes\mathbb C^{\mathrm{DB}}$ by
--   $$
--   \mathsf{cO}\,|s\rangle|D\rangle=|s\rangle|D\oplus q(s)\rangle ,
--   $$
--   i.e. a query on key $a$ and input $y$ toggles the entry $(a,y)$ of the database. The **compressed run** is $(\mathsf{cO}\,U)^T=\mathsf{cO}(U_T\otimes I)\cdots\mathsf{cO}(U_1\otimes I)$.
--
--   Under the Fourier transform of the oracle register the phase $R(p)$ becomes the toggle of $p$, so the compressed run is the purified run.
--
--   **Formalization Note** `liftL M` is $M\otimes I$ and `liftR M` is $I\otimes M$ (Kronecker products, algorithm register first). A basis state with $q(s)=\bot$ leaves the database unchanged.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, p.18 (PDF p.21); §5.3, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_PreprocOWS_Alg
import Definitions.Def_PreprocOWS_DB
open Matrix

namespace PreprocOWS

/-- `M ⊗ I`: an operator on the algorithm's register `α` acting as the identity on the database
register (arXiv:2610.02101, §5.1, p.18: `U` and `Π_k` "act on the first registers"). -/
def liftL {α β : Type*} [DecidableEq β] (M : Matrix α α ℂ) : Matrix (α × β) (α × β) ℂ :=
  Matrix.kronecker M 1

/-- `I ⊗ M`: an operator on the database register acting as the identity on the algorithm's
register. -/
def liftR {α β : Type*} [DecidableEq α] (M : Matrix β β ℂ) : Matrix (α × β) (α × β) ℂ :=
  Matrix.kronecker 1 M

/-- The **compressed phase oracle** `cO |s⟩|D⟩ = |s⟩|D ⊕ q(s)⟩` of an algorithm `A`, Dong–Lombardi,
arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, p.18 (PDF p.21) and §5.3, p.20
(PDF p.23): "cO |a,y⟩|D⟩ = |a,y⟩|D ⊕ (a,y)⟩ for a query on key a and input y".

**Formalization Note.** With the query map `q` of `Alg`, a basis state `s` with `q(s) = none`
leaves the database unchanged. -/
def cO {S T K N w : ℕ} (A : Alg S T K N w) :
    Matrix (Ω S N w × DB K N) (Ω S N w × DB K N) ℂ :=
  Matrix.of fun s' s => if s'.1 = s.1 ∧ s'.2 = togOpt (A.q s.1) s.2 then 1 else 0

/-- The compressed run `(cO U)^T = cO (U_T ⊗ I) ⋯ cO (U_1 ⊗ I)` (arXiv:2610.02101, §5.1, p.18). -/
def cRun {S T K N w : ℕ} (A : Alg S T K N w) :
    Matrix (Ω S N w × DB K N) (Ω S N w × DB K N) ℂ :=
  layeredRun (cO A) (fun i => liftL (A.U i : Matrix (Ω S N w) (Ω S N w) ℂ))

end PreprocOWS


