-- Prove2me | Definitions.Def_RInf_braid_v2
-- name    : RInf_braid_v2
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T14:53:23.33633+00:00
-- url     : https://prove2.me/theorems/4ca427fa-661b-41f8-8d24-4fe358ca6ff9
-- title:
--   The world layer (corrected): the pure Artin braid group with its commutator layer, without the eigenvalue-one and transfer axioms
-- statement:
--   The definitional world-layer setup of the pure Artin braid group $P_n$ on $n$ strings, correcting the superseded `RInf_braid`. It bundles only the data of the setting: the second commutator layer $Q = \Gamma_2(P_n)/\Gamma_3(P_n)$ of the lower central series as an abstract free abelian group, together with the biadditive commutator pairing $\mathrm{comm}: P_n \times P_n \to Q$ through which the layer is generated; the induced action $\mathrm{act}$ of the automorphisms of $P_n$ on the layer, compatible with the pairing; and the standard coordinates identifying $Q$ with the integer lattice $\mathbb{Z}^{\binom{n}{3}}$ (the basis of triples, equation (5)). Crucially, this setup does NOT assume the paper's results as axioms: the factorization of the induced action through the representation $\rho$ of the symmetric group $S_{n+1}$ (equation (8)), the eigenvalue-one property of every representation value (Theorems 8 and 11), and the Reidemeister transfer carrying infinite Reidemeister number from the layer to the braid group (Remark 1 / Dekimpe–Gonçalves Lemma 2.2) are all theorems to be proved. Assuming them, as the superseded `BraidWorld` did, made the main theorem (Theorem 12) a trivial consequence and left Sections 2–3 unformalized.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 2 (the commutator layer Gamma_2(P_n)/Gamma_3(P_n), its basis (5), and the induced action phi_2); arXiv:2006.08286. Corrects RInf_braid by removing the rep_eigen (Theorem 11) and transfer (Remark 1 / Lemma 2.2) axiom fields, and the equation-(8) factorization fields.

import Mathlib
import Definitions.Def_RInf_alg

/-!
# The world layer (corrected): the pure Artin braid group with its commutator layer

The definitional setup of the RInf mission for Karel Dekimpe, Daciberg Lima
Goncalves and Oscar Ocampo, "The R-infinity property for pure Artin braid
groups" (Monatshefte fur Mathematik 195 (2021), 15-33). It bundles only the
DATA of the pure braid group world on n strings: the second commutator layer
Q = Gamma_2(P_n)/Gamma_3(P_n) of the lower central series as an abstract free
abelian group with the biadditive commutator pairing through which it is
generated; the induced action of the automorphisms of the braid group on the
layer; and the standard coordinates identifying the layer with the integer
lattice of rank the number of triples of strings (the basis (5)).

This setup deliberately does NOT assume the paper's results. The factorization
of the induced action through the representation of the symmetric group
S_{n+1} (equation (8)), the eigenvalue-one property of the representation
values (Theorems 8 and 11), and the Reidemeister transfer carrying infinitude
from the layer to the braid group (Remark 1 / Dekimpe-Goncalves Lemma 2.2) are
theorems to be proved, not fields of the setup. Assuming them would make the
main theorem (Theorem 12) a trivial consequence and leave Sections 2-3
unformalized.
-/

namespace RInf

/-- The definitional setup of the pure Artin braid group on n strings: the
commutator layer Q with the biadditive pairing comm of commutators, the induced
action act of the automorphisms on the layer, and the standard coordinates on
the layer of rank the number of triples of strings. The factorization through
the symmetric-group representation, the eigenvalue-one property, and the
Reidemeister transfer are NOT assumed here; they are the theorems the mission
proves. -/
structure BraidSetup (n : Nat) (P Q : Type*) [Group P] [AddCommGroup Q] where
  comm : P → P → Q
  comm_left : ∀ (g1 g2 h : P), comm (g1 * g2) h = comm g1 h + comm g2 h
  comm_right : ∀ (g h1 h2 : P), comm g (h1 * h2) = comm g h1 + comm g h2
  comm_surj : ∀ q : Q, ∃ g h : P, comm g h = q
  act : (P ≃* P) → Q ≃+ Q
  act_comm : ∀ (α : P ≃* P) (g h : P), act α (comm g h) = comm (α g) (α h)
  coord : Q ≃+ (Fin (Nat.choose n 3) → Int)

end RInf


