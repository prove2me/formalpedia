-- Prove2me | Definitions.Def_SymThrWires_Main_Tomography
-- name    : SymThrWires_Main_Tomography
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:15:55.9307+00:00
-- url     : https://prove2.me/theorems/ff99142e-203a-455e-bdd2-041d7b525983
-- title:
--   Modular push-forwards F_p, D′ = 1 + Σ(p − 1), and S(q) = Σ m φ(m)
-- statement:
--   Let $P$ be a nonempty finite set of primes and $D'=1+\sum_{p\in P}(p-1)$. For a finitely supported function $F:\mathbb Z^d\to\mathbb Q$ and a prime $p$, the **modular push-forward** is
--   $$F_p(\rho)=\sum_{u\equiv\rho\ (\mathrm{mod}\ p)}F(u),\qquad\rho\in(\mathbb Z/p\mathbb Z)^d,$$
--   the total mass of each residue class. With Euler's totient $\varphi$, $S(q)=\sum_{m=1}^q m\,\varphi(m)$ and $S(0)=0$.
--
--   These are the data of the discrete-tomography Lemma E.5, by which residue counts determine a score distribution.
--
--   **Formalization Note.** $F$ is a `Finsupp` `(Fin d → ℤ) →₀ ℚ`; the push-forward sums over its support, which is the displayed sum since $F$ vanishes elsewhere. Residues are taken coordinatewise in `ZMod p`.
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 52, §E.11 (D′, F_p); p. 52, §E.13 (S(q))

import Mathlib

/-!
# Modular push-forwards and the totient sum `S(q)`

Dev Nag, *Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits*, STOC 2027
submission, Zenodo doi:10.5281/zenodo.23847026, p. 52 (§E.11: `D′`, `F_p`) and p. 52 (§E.13:
`S(q)`).
-/

namespace SymThrWires.Main

/-- `D′ = 1 + Σ_{p ∈ P} (p − 1)` for a finite set `P` of primes (§E.11). -/
def Dprime (P : Finset ℕ) : ℕ := 1 + ∑ p ∈ P, (p - 1)

open Classical in
/-- The **modular push-forward** `F_p(ρ) = Σ_{u ≡ ρ (mod p)} F(u)`, `ρ ∈ (Z/pZ)^d`, of a finitely
supported `F : Z^d → Q` (§E.11). -/
noncomputable def pushforward {d : ℕ} (F : (Fin d → ℤ) →₀ ℚ) (p : ℕ) (ρ : Fin d → ZMod p) : ℚ :=
  ∑ u ∈ F.support.filter (fun u => (fun i => ((u i : ℤ) : ZMod p)) = ρ), F u

/-- `S(q) = Σ_{m=1}^{q} m φ(m)`, with `S(0) = 0` (§E.13). -/
def totientSum (q : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 q, m * Nat.totient m

end SymThrWires.Main


