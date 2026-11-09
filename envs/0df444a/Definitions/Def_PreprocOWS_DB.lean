-- Prove2me | Definitions.Def_PreprocOWS_DB
-- name    : PreprocOWS_DB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:50.179229+00:00
-- url     : https://prove2.me/theorems/389e393c-f6bd-4241-9159-e2f1926b34ca
-- title:
--   Databases $D\subseteq[K]\times[N]$, toggles $T_{k,x}$, support on small databases
-- statement:
--   The **database register** of the compressed oracle has basis $\{|D\rangle : D\subseteq[K]\times[N]\}$; for a $\pm1$-valued uniform oracle it is the Fourier basis of the oracle register, and the uniformly random oracle is $|\emptyset\rangle$. For an entry $p=(k,x)$,
--   $$
--   T_{k,x}|D\rangle=|D\oplus\{(k,x)\}\rangle
--   $$
--   flips the presence of $(k,x)$ ($\oplus$ is symmetric difference); for an optional entry, $D\oplus\bot=D$. A state $\psi$ on (algorithm register)$\otimes$(database register) is **supported on databases of size $\le\ell$** if $\psi(a,D)=0$ whenever $|D|>\ell$. The size of row $k$ of $D$ is $|D_k|=|\{x:(k,x)\in D\}|$.
--
--   These are the objects in which the trace moment is computed and in which Lemma 5.3 is stated.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, p.18 (PDF p.21); Lemma 5.3, p.18; §5.3, pp.20–21 (PDF pp.23–24)

import Mathlib
open Matrix

namespace PreprocOWS

/-- **Compressed-oracle databases** `D ⊆ [K] × [N]`, Dong–Lombardi, arXiv:2610.02101 (version of
2026-11-02, sha256 7a0bd8da…), §5.1, p.18 (PDF p.21) and §5.3, p.20 (PDF p.23). For a `±1`-valued
random oracle the database register has basis `{|D⟩ : D ⊆ [K] × [N]}` (the Fourier basis of the
oracle register); the uniformly random oracle is `|∅⟩`. -/
abbrev DB (K N : ℕ) : Type := Finset (Fin K × Fin N)

/-- The toggle `D ↦ D ⊕ o` by an optional entry: `D ⊕ none = D`, `D ⊕ some p = D ⊕ {p}`
(symmetric difference), arXiv:2610.02101, §5.3, p.20 ("cO |a,y⟩|D⟩ = |a,y⟩|D ⊕ (a,y)⟩"). -/
def togOpt {K N : ℕ} : Option (Fin K × Fin N) → DB K N → DB K N
  | none, D => D
  | some p, D => symmDiff D {p}

/-- The operator `T_{k,x} |D⟩ = |D ⊕ {(k,x)}⟩` on the database register, which flips the presence
of the entry `p = (k,x)` (arXiv:2610.02101, §5.1, p.18, PDF p.21). -/
def togMat {K N : ℕ} (p : Fin K × Fin N) : Matrix (DB K N) (DB K N) ℂ :=
  Matrix.of fun D' D => if D' = symmDiff D {p} then 1 else 0

/-- A state `ψ` on (algorithm register) ⊗ (database register) is **supported on databases of size
`≤ ℓ`**: `ψ(a, D) = 0` whenever `|D| > ℓ` (arXiv:2610.02101, Lemma 5.3, p.18, PDF p.21). -/
def SupportedLE {α : Type*} {K N : ℕ} (ℓ : ℕ) (ψ : α × DB K N → ℂ) : Prop :=
  ∀ a D, ℓ < D.card → ψ (a, D) = 0

/-- The size `|D_k| = |{x : (k,x) ∈ D}|` of row `k` of a database (arXiv:2610.02101, §5.3, p.21,
PDF p.24: "Write S_k := {x : (k,x) ∈ S}"). -/
def rowCard {K N : ℕ} (D : DB K N) (k : Fin K) : ℕ :=
  (D.filter fun p => p.1 = k).card

end PreprocOWS


